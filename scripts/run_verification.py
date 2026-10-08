#!/usr/bin/env python3
"""Run fresh verification; record wall-clock timestamps and monotonic durations."""
import argparse
from datetime import datetime, timezone
import json
import os
import re
import shutil
import subprocess
import sys
import time
from uuid import uuid4
from audit_sources import ROOT, project_sources
from report_verification import digest


def now():
    return datetime.now(timezone.utc).isoformat(timespec='microseconds')


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--prepare-cache', action='store_true', help='Fetch locked dependencies and mathlib cache')
    args = parser.parse_args()
    start, tick = now(), time.monotonic()
    run_id = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ') + '-' + uuid4().hex[:8]
    run_dir = ROOT / 'verification/runs' / run_id
    run_dir.mkdir(parents=True, exist_ok=False)
    if output := os.environ.get('GITHUB_OUTPUT'):
        with open(output, 'a') as stream:
            stream.write(f'run_dir={run_dir.relative_to(ROOT)}\n')
    child_environment = os.environ.copy()
    # Nested regression fixtures must not replace this job step's artifact path.
    child_environment.pop('GITHUB_OUTPUT', None)
    run = {'run_id': run_id, 'started_at_utc': start, 'status': 'running', 'steps': [],
           'git_head_before_run': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()}
    wrapper = ['bash', str(ROOT / 'scripts/with_lean.sh')]
    py = [sys.executable]
    stages = [('regression_tests', [*py, '-m', 'unittest', 'discover', '-s', 'tests', '-v'], 'regression_tests.log'),
              ('source_audit', [*py, 'scripts/audit_sources.py', '--output-dir', str(run_dir)], 'source_audit.log')]
    if args.prepare_cache:
        imports = sorted({name for source in project_sources(ROOT)
                          for name in re.findall(r'^import (Mathlib\.\S+)', source.read_text(), re.M)})
        if not imports:
            raise ValueError('No mathlib imports found for cache preparation')
        stages.append(('cache', [*wrapper, 'lake', 'exe', 'cache', 'get', *imports], 'cache.log'))
    stages += [('environment', [*py, 'scripts/check_environment.py', '--output-dir', str(run_dir)], 'environment.log'),
               ('build', [*wrapper, 'lake', 'build'], 'build.log'),
               ('axioms', [*wrapper, 'lake', 'env', 'lean', 'AxiomAudit.lean'], 'axioms.log'),
               ('report', [*py, 'scripts/report_verification.py', '--run-dir', str(run_dir)], 'report.log')]
    exit_code = 1
    try:
        for stage, command, log in stages:
            step_tick = time.monotonic()
            step = {'stage': stage, 'command': command, 'log': log, 'started_at_utc': now()}
            run['steps'].append(step)
            write_json(run_dir / 'run.json', run)
            print(f"[{step['started_at_utc']}] {stage}: {' '.join(command)}", flush=True)
            with (run_dir / log).open('w') as stream:
                try:
                    process = subprocess.Popen(command, cwd=ROOT, env=child_environment,
                                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
                    for line in process.stdout:
                        stream.write(line)
                        stream.flush()
                        print(line, end='', flush=True)
                    code = process.wait()
                except OSError as error:
                    stream.write(str(error) + '\n')
                    code = 127
            step.update(exit_code=code, ended_at_utc=now(), elapsed_seconds=time.monotonic() - step_tick,
                        log_sha256=digest(run_dir / log))
            if stage == 'source_audit' and code == 0:
                run['lean_source_sha256'] = {str(p.relative_to(ROOT)): digest(p)
                    for p in [*project_sources(ROOT), ROOT / 'AxiomAudit.lean']}
            write_json(run_dir / 'run.json', run)
            print(f"[{step['ended_at_utc']}] {stage}: exit={code}, elapsed={step['elapsed_seconds']:.6f}s", flush=True)
            if code:
                exit_code = code if code > 0 else 1
                break
        else:
            exit_code = 0
    finally:
        run.update(ended_at_utc=now(), elapsed_seconds=time.monotonic() - tick,
                   exit_code=exit_code, status='success' if exit_code == 0 else 'failed')
        write_json(run_dir / 'run.json', run)
        if (run_dir / 'results.json').exists() and exit_code == 0:
            result = json.loads((run_dir / 'results.json').read_text())
        else:
            result = {'run_id': run_id,
                      'build_success': any(s['stage'] == 'build' and s.get('exit_code') == 0 for s in run['steps']),
                      'verification_success': False,
                      'main_theorem_proved': False, 'main_theorem_formal_statement_implemented': False}
        result.update(verification_success=exit_code == 0, started_at_utc=start,
                      ended_at_utc=run['ended_at_utc'], elapsed_seconds=run['elapsed_seconds'],
                      exit_code=exit_code, stage_exit_codes={s['stage']: s.get('exit_code') for s in run['steps']})
        write_json(run_dir / 'results.json', result)
        write_json(ROOT / 'verification/latest.json', {'run_id': run_id, 'path': str(run_dir.relative_to(ROOT)),
                                                       'exit_code': exit_code})
        for name in ('build.log', 'axioms.log', 'declarations.json', 'results.json'):
            source = run_dir / name
            if source.exists():
                shutil.copy2(source, ROOT / 'verification' / name)
            elif name.endswith('.log'):
                (ROOT / 'verification' / name).write_text(f'Not executed in run {run_id}\n')
            elif name == 'declarations.json':
                write_json(ROOT / 'verification' / name, [])
        print(json.dumps({'run_id': run_id, 'exit_code': exit_code, 'started_at_utc': start,
                          'ended_at_utc': run['ended_at_utc'], 'elapsed_seconds': run['elapsed_seconds']}, indent=2))
    return exit_code


if __name__ == '__main__':
    sys.exit(main())
