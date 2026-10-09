#!/usr/bin/env python3
"""Run every generated #print axioms command once, with optional parallel shards."""
import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import json
from pathlib import Path
import re
import subprocess
import sys
import time
from audit_sources import ROOT, require_unique
from report_verification import check_coverage, digest


def now():
    return datetime.now(timezone.utc).isoformat(timespec='microseconds')


def shard_entries(entries, commands, jobs):
    if jobs < 1:
        raise ValueError('Axiom audit jobs must be positive')
    require_unique([e['name'] for e in entries], 'inventory names')
    require_unique(commands, 'generated audit command names')
    if Counter(commands) != Counter(e['name'] for e in entries):
        raise ValueError('Generated audit commands differ from this run inventory')
    by_name = {e['name']: e for e in entries}
    return [[by_name[n] for n in commands[i::jobs]] for i in range(min(jobs, len(commands)))]


def run_shard(directory, number, entries, runner=('lean', '-DautoImplicit=false')):
    source = directory / f'Shard{number:02d}.lean'
    log = directory / f'Shard{number:02d}.log'
    record = directory / f'Shard{number:02d}.json'
    if any(p.exists() for p in (source, log, record)):
        raise ValueError('Axiom shard output already exists')
    source.write_text('import ASGinzburg\n\n' +
                      '\n'.join('#print axioms ' + e['name'] for e in entries) + '\n')
    started, tick = now(), time.monotonic()
    command = [*runner, str(source)]
    with log.open('w') as stream:
        try:
            code = subprocess.run(command, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT).returncode
        except OSError as error:
            stream.write(str(error) + '\n')
            code = 127
    data = {'shard': number, 'command': command, 'started_at_utc': started,
            'ended_at_utc': now(), 'elapsed_seconds': time.monotonic() - tick,
            'exit_code': code, 'declarations': [e['name'] for e in entries],
            'source': source.name, 'source_sha256': digest(source),
            'log': log.name, 'log_sha256': digest(log), 'strict_coverage': False}
    if code == 0:
        try:
            _, axioms = check_coverage(entries, log.read_text())
            data.update(strict_coverage=True, axioms=sorted(axioms))
        except ValueError as error:
            data.update(exit_code=1, certification_error=str(error))
    record.write_text(json.dumps(data, indent=2) + '\n')
    return data


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--run-dir', type=Path, required=True)
    parser.add_argument('--jobs', type=int, default=1)
    args = parser.parse_args()
    run_dir = args.run_dir.resolve()
    audit = ROOT / 'AxiomAudit.lean'
    audit_hash = digest(audit)
    commands = re.findall(r'^#print axioms (\S+)$', audit.read_text(), re.M)
    entries = json.loads((run_dir / 'declarations.json').read_text())
    groups = shard_entries(entries, commands, args.jobs)
    directory = run_dir / 'axiom_shards'
    directory.mkdir(exist_ok=False)
    started, tick = now(), time.monotonic()
    with ThreadPoolExecutor(max_workers=len(groups)) as pool:
        futures = [pool.submit(run_shard, directory, i + 1, group) for i, group in enumerate(groups)]
        records = [f.result() for f in futures]
    logs = [(directory / record['log']).read_text() for record in records]
    success = all(r['exit_code'] == 0 and r['strict_coverage'] for r in records)
    if audit_hash != digest(audit):
        success = False
    if success:
        check_coverage(entries, '\n'.join(logs))
    (run_dir / 'axiom_shards.json').write_text(json.dumps({
        'started_at_utc': started, 'ended_at_utc': now(),
        'elapsed_seconds': time.monotonic() - tick, 'jobs': len(groups),
        'audit_source_sha256': audit_hash, 'shards': records, 'success': success}, indent=2) + '\n')
    for log in logs:
        print(log, end='' if log.endswith('\n') else '\n')
    for record in records:
        if error := record.get('certification_error'):
            print(error, file=sys.stderr)
    return 0 if success else 1


if __name__ == '__main__':
    sys.exit(main())
