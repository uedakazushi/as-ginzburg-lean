#!/usr/bin/env python3
"""Archive an upgrade completion only after checking a fresh successful run.

This never builds Lean, rewrites verification aliases, edits sources or commits.
Run with the verification workspace quiescent; existing completion files are
never overwritten. Diagnostic copies retain their original intermediate status.
"""
import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import io
import json
import math
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT / 'scripts'))
from audit_sources import inventory, project_sources, require_unique
from report_verification import check_coverage, digest, TOOLCHAIN, MATHLIB

BASELINE = '88ac9e307b51043e5378c3eaebbbf927a6f6cf21'
DECLARATIONS = 6909
PUBLIC_SOURCE_FILES = 1373
STAGES = ['regression_tests', 'source_audit', 'environment', 'build', 'axioms', 'report']
PROTECTED = ['recovery/', 'checkpoints/', 'verification/runs/',
             'verification/resume_20261010/', 'docs/source.pdf']


def require(condition, message):
    if not condition:
        raise ValueError(message)


def git(*args, data=None):
    return subprocess.check_output(['git', '--no-optional-locks', *args], cwd=ROOT, input=data)


def read_json(path):
    return json.loads(path.read_text())


def utc(value):
    parsed = datetime.fromisoformat(value)
    require(parsed.utcoffset() == timezone.utc.utcoffset(parsed), 'Timestamp must be UTC')
    return parsed


def timing(record):
    start, end = utc(record['started_at_utc']), utc(record['ended_at_utc'])
    duration = record['elapsed_seconds']
    require(type(duration) in (int, float) and math.isfinite(duration) and duration >= 0,
            'Missing or invalid measured duration')
    require(start <= end, 'End timestamp precedes start')
    return start, end


def run_file(run_dir, relative):
    path = run_dir / relative
    require(path.is_file() and not path.is_symlink() and path.resolve().is_relative_to(run_dir),
            f'Missing or unsafe run evidence: {relative}')
    return path


def check_history(run_dir):
    """Compare raw tracked blobs and executable modes, including unstaged edits."""
    rows = git('ls-tree', '-r', '-z', BASELINE, '--', *PROTECTED).split(b'\0')
    baseline = {}
    for row in filter(None, rows):
        header, path = row.split(b'\t', 1)
        mode, kind, blob = header.decode().split()
        require(kind == 'blob' and mode in ('100644', '100755'), 'Unsupported historical entry')
        baseline[path.decode()] = (mode, blob)
    require(baseline, 'Empty historical baseline')
    new_prefix = str(run_dir.relative_to(ROOT)) + '/'
    require(not any(p.startswith(new_prefix) for p in baseline), 'Selected run is not new')
    indexed = {}
    for row in filter(None, git('ls-files', '--stage', '-z', '--', *PROTECTED).split(b'\0')):
        header, path = row.split(b'\t', 1)
        relative = path.decode()
        if relative.startswith(new_prefix):
            continue
        mode, blob, stage = header.decode().split()
        require(stage == '0', f'Unmerged historical entry: {relative}')
        indexed[relative] = (mode, blob)
    require(indexed == baseline, 'Historical index entries were added, removed or changed')
    paths = sorted(baseline)
    for relative in paths:
        path = ROOT / relative
        require(path.is_file() and not path.is_symlink() and path.resolve().is_relative_to(ROOT),
                f'Historical file missing or unsafe: {relative}')
        mode = '100755' if path.stat().st_mode & 0o111 else '100644'
        require(mode == baseline[relative][0], f'Historical file mode changed: {relative}')
        require('\n' not in str(path) and '\r' not in str(path), 'Unsupported historical filename')
    blobs = git('hash-object', '--no-filters', '--stdin-paths',
                data=('\n'.join(str(ROOT / p) for p in paths) + '\n').encode()).decode().splitlines()
    require(len(blobs) == len(paths), 'Incomplete historical hash comparison')
    changed = [p for p, blob in zip(paths, blobs) if blob != baseline[p][1]]
    require(not changed, f'Historical contents changed: {changed[:10]}')
    return {'baseline_commit': BASELINE, 'tracked_files_checked': len(paths),
            'protected_paths': PROTECTED, 'new_run_exception': str(run_dir.relative_to(ROOT)),
            'baseline_blob_manifest_sha256': hashlib.sha256(
                json.dumps(baseline, sort_keys=True).encode()).hexdigest(), 'unchanged': True}


def baseline_inventory():
    archive = git('archive', BASELINE, '--', 'ASGinzburg.lean', 'ASGinzburg/')
    with tempfile.TemporaryDirectory(prefix='as-ginzburg-upgrade-baseline-') as directory:
        root = Path(directory)
        with tarfile.open(fileobj=io.BytesIO(archive)) as stream:
            for member in stream:
                path = root / member.name
                require(path.resolve().is_relative_to(root), 'Unsafe baseline archive path')
                if member.isdir():
                    path.mkdir(parents=True, exist_ok=True)
                else:
                    require(member.isfile(), 'Unsupported baseline source entry')
                    path.parent.mkdir(parents=True, exist_ok=True)
                    with stream.extractfile(member) as source, path.open('wb') as target:
                        shutil.copyfileobj(source, target)
        return inventory(root)


def validate_semantic_review(public_hashes, entries):
    """Require a successful independent review of these exact frozen sources."""
    path = ROOT / 'work/lean-upgrade/statement-review-final.json'
    require(path.is_file() and not path.is_symlink() and path.resolve().is_relative_to(ROOT),
            'Missing or unsafe final semantic review')
    review_digest = digest(path)
    review = read_json(path)
    require(digest(path) == review_digest, 'Final semantic review changed while reading')
    require(review['baseline_commit'] == BASELINE and review['lean_toolchain'] == TOOLCHAIN,
            'Final semantic review baseline or toolchain differs')
    require(review['final_verification_freeze'] is True and
            review['semantic_review_success'] is True,
            'Final semantic review is provisional or unsuccessful')
    require(len(public_hashes) == PUBLIC_SOURCE_FILES and
            review['public_source_files'] == PUBLIC_SOURCE_FILES and
            review['public_math_modules'] == PUBLIC_SOURCE_FILES - 1 and
            review['source_sha256'] == public_hashes,
            'Final semantic review source coverage is incomplete or stale')
    require(len(entries) == DECLARATIONS and
            review['declarations_before'] == review['declarations_after'] == DECLARATIONS and
            review['declaration_names_and_kinds'] == {e['name']: e['kind'] for e in entries},
            'Final semantic review declaration inventory differs')
    for field in ('declaration_names_and_kinds_preserved', 'namespace_scopes_preserved',
                  'universe_declarations_preserved', 'ambient_variables_includes_omits_preserved'):
        require(review[field] is True, f'Final semantic review did not preserve {field}')
    require(review['definition_semantics_review']['underlying_maps_and_objects_preserved'] is True,
            'Final semantic review did not preserve the original maps and objects')
    for field in ('new_mathematical_hypotheses_found', 'weakened_mathematical_conclusions_found',
                  'unexpected_declaration_signature_changes', 'concrete_semantic_concerns'):
        require(review[field] == [], f'Final semantic review has unresolved {field}')
    headers = review['changed_headers']
    require(isinstance(headers, list) and review['changed_header_count'] == len(headers) and
            review['header_classification_count_verified'] is True and
            all(isinstance(h, dict) and isinstance(h.get('classification'), str) and
                h['classification'] for h in headers) and
            review['changed_header_classifications'] == dict(Counter(h['classification'] for h in headers)),
            'Final semantic review header classification is incomplete')
    require(utc(review['reviewed_at_utc']) <= utc(review['manual_review_completed_at_utc']),
            'Final semantic review timestamps are inconsistent')
    require(digest(path) == review_digest, 'Final semantic review changed during validation')
    return {'source': str(path.relative_to(ROOT)), 'sha256': review_digest,
            'semantic_review_success': True, 'final_verification_freeze': True,
            'reviewed_at_utc': review['reviewed_at_utc'],
            'manual_review_completed_at_utc': review['manual_review_completed_at_utc'],
            'public_source_files': PUBLIC_SOURCE_FILES, 'declaration_count': DECLARATIONS,
            'changed_header_count': len(headers)}


def validate(run_dir):
    require(TOOLCHAIN == 'leanprover/lean4:v4.34.1' and
            MATHLIB == 'd13f23b723b8a846827a245b89c10fc7d3f11612', 'Validator pins changed')
    require(run_dir.parent == (ROOT / 'verification/runs').resolve() and run_dir.is_dir(),
            '--run-dir must be a direct child of verification/runs')
    run = read_json(run_file(run_dir, 'run.json'))
    require(run['run_id'] == run_dir.name and run['status'] == 'success' and
            type(run['exit_code']) is int and run['exit_code'] == 0, 'Run is not successful')
    start, end = timing(run)
    migration_start = read_json(ROOT / 'verification/lean_upgrade/start.json')
    require(migration_start['baseline_head'] == BASELINE and
            start >= utc(migration_start['started_at_utc']), 'Run predates this upgrade')
    stages = [step['stage'] for step in run['steps']]
    require(stages in (STAGES, STAGES[:2] + ['cache'] + STAGES[2:]),
            'Missing, duplicated, reordered or unexpected verification stage')
    evidence = {str(p.relative_to(ROOT)): digest(p) for p in
                (run_file(run_dir, name) for name in
                 ('run.json', 'results.json', 'environment.json', 'declarations.json',
                  'axioms.log', 'axiom_shards.json'))}
    previous_end = start
    for step in run['steps']:
        require(type(step['exit_code']) is int and step['exit_code'] == 0, 'Failed verification stage')
        step_start, step_end = timing(step)
        require(previous_end <= step_start <= step_end <= end, 'Inconsistent stage timestamps')
        previous_end = step_end
        path = run_file(run_dir, step['log'])
        require(digest(path) == step['log_sha256'], f'Stage log changed: {step["stage"]}')
        evidence[str(path.relative_to(ROOT))] = digest(path)
        command = step['command']
        require(isinstance(command, list) and all(isinstance(s, str) for s in command),
                'Invalid recorded stage command')
        stage = step['stage']
        if stage == 'regression_tests':
            require(command[1:] == ['-m', 'unittest', 'discover', '-s', 'tests', '-v'],
                    'Unexpected regression command')
        elif stage in ('source_audit', 'environment', 'report'):
            script = {'source_audit': 'audit_sources.py', 'environment': 'check_environment.py',
                      'report': 'report_verification.py'}[stage]
            flag = '--run-dir' if stage == 'report' else '--output-dir'
            require(command[1:] == ['scripts/' + script, flag, str(run_dir)],
                    f'Unexpected {stage} command')
        else:
            require(command[:3] == ['bash', str(ROOT / 'scripts/with_lean.sh'), 'lake'],
                    f'Unexpected {stage} wrapper')
            if stage == 'build':
                require(command[3:] == ['build', 'ASGinzburg'], 'Unexpected build target')
            elif stage == 'axioms':
                require(len(command) == 10 and command[3] == 'env' and
                        command[5:9] == ['scripts/run_axiom_audit.py', '--run-dir', str(run_dir),
                                         '--jobs'] and command[9].isdigit() and int(command[9]) > 0,
                        'Unexpected exhaustive audit command')
            else:
                require(command[3:6] == ['exe', 'cache', 'get'] and len(command) > 6,
                        'Unexpected optional cache command')
    entries = inventory(ROOT)
    require(len(entries) == DECLARATIONS and read_json(run_dir / 'declarations.json') == entries,
            'Current declaration inventory differs from this run')
    before = baseline_inventory()
    require(len(before) == DECLARATIONS and
            Counter((e['name'], e['kind']) for e in before) ==
            Counter((e['name'], e['kind']) for e in entries), 'Original declaration names/kinds changed')
    commands = re.findall(r'^#print axioms (\S+)$', (ROOT / 'AxiomAudit.lean').read_text(), re.M)
    require_unique(commands, 'audit command names')
    require(Counter(commands) == Counter(e['name'] for e in entries), 'Generated audit coverage differs')
    names, axioms = check_coverage(entries, (run_dir / 'axioms.log').read_text())
    require(len(names) == DECLARATIONS, 'Incomplete axiom coverage')
    shards = read_json(run_dir / 'axiom_shards.json')
    require(shards['success'] is True and shards['audit_source_sha256'] == digest(ROOT / 'AxiomAudit.lean'),
            'Axiom shard summary failed or is stale')
    shard_start, shard_end = timing(shards)
    axiom_step = next(step for step in run['steps'] if step['stage'] == 'axioms')
    axiom_start, axiom_end = timing(axiom_step)
    require(axiom_start <= shard_start <= shard_end <= axiom_end, 'Axiom summary predates this stage')
    require(type(shards['jobs']) is int and shards['jobs'] == len(shards['shards']) > 0,
            'Incomplete axiom shard summary')
    require([p['shard'] for p in shards['shards']] == list(range(1, shards['jobs'] + 1)),
            'Missing or duplicated shard numbers')
    shard_names, shard_logs = [], []
    for shard in shards['shards']:
        require(type(shard['exit_code']) is int and shard['exit_code'] == 0 and
                shard['strict_coverage'] is True, 'Axiom shard failed')
        part_start, part_end = timing(shard)
        require(shard_start <= part_start <= part_end <= shard_end, 'Axiom shard predates this audit')
        source = run_file(run_dir, 'axiom_shards/' + shard['source'])
        log = run_file(run_dir, 'axiom_shards/' + shard['log'])
        record = run_file(run_dir, f'axiom_shards/Shard{shard["shard"]:02d}.json')
        require(read_json(record) == shard, 'Axiom shard record differs from summary')
        require(shard['source'] == f'Shard{shard["shard"]:02d}.lean' and
                shard['log'] == f'Shard{shard["shard"]:02d}.log' and
                shard['command'] == ['lean', '-DautoImplicit=false', str(source)],
                'Unexpected axiom shard compilation command')
        require(digest(source) == shard['source_sha256'] and digest(log) == shard['log_sha256'],
                'Axiom shard evidence changed')
        selected = [{'name': name} for name in shard['declarations']]
        text = log.read_text()
        _, shard_axioms = check_coverage(selected, text)
        require(shard['axioms'] == sorted(shard_axioms), 'Shard axiom summary differs from its log')
        shard_logs.append(text if text.endswith('\n') else text + '\n')
        expected_source = 'import ASGinzburg\n\n' + '\n'.join(
            '#print axioms ' + name for name in shard['declarations']) + '\n'
        require(source.read_text() == expected_source,
                'Axiom shard commands differ')
        shard_names.extend(shard['declarations'])
        evidence.update({str(p.relative_to(ROOT)): digest(p) for p in (source, log, record)})
    require_unique(shard_names, 'axiom shard names')
    require(Counter(shard_names) == Counter(names), 'Incomplete axiom shard coverage')
    require((run_dir / 'axioms.log').read_text() == ''.join(shard_logs),
            'Combined axiom log differs from this run\'s shard logs')
    hashes = {str(p.relative_to(ROOT)): digest(p) for p in [*project_sources(ROOT), ROOT / 'AxiomAudit.lean']}
    semantic_review = validate_semantic_review(
        {p: sha for p, sha in hashes.items() if p != 'AxiomAudit.lean'}, entries)
    evidence[semantic_review['source']] = semantic_review['sha256']
    result = read_json(run_dir / 'results.json')
    require(hashes == run['lean_source_sha256'] == result['lean_source_sha256'], 'Public sources changed')
    require(result['run_id'] == run_dir.name and result['verification_success'] is True and
            result['build_success'] is True and type(result['exit_code']) is int and result['exit_code'] == 0,
            'Final verification result failed')
    require(result['stage_exit_codes'] == {step['stage']: 0 for step in run['steps']} and
            result['declaration_count'] == result['unique_declaration_count'] == DECLARATIONS and
            result['kernel_axiom_dependencies'] == sorted(axioms), 'Final certificate disagrees with evidence')
    require(result['module_count'] == len(hashes) - 2 and
            result['declaration_kinds'] == dict(Counter(e['kind'] for e in entries)) and
            result['theorem_count'] == sum(e['kind'] in ('theorem', 'lemma') for e in entries) and
            result['definitions_theorems_and_types'] == sum(e['kind'] != 'instance' for e in entries) and
            all(result[key] == [] for key in ('missing_theorems', 'unchecked_proof_dependencies',
                                            'source_placeholders')) and
            result['main_theorem_proved'] is False, 'Final certificate claim differs from audited scope')
    require(all(result[k] == run[k] for k in ('started_at_utc', 'ended_at_utc', 'elapsed_seconds')),
            'Final result timings disagree')
    env = read_json(run_dir / 'environment.json')
    environment_step = next(step for step in run['steps'] if step['stage'] == 'environment')
    require(read_json(run_file(run_dir, environment_step['log'])) == env,
            'Environment stage log differs from its JSON evidence')
    require(env['lean_toolchain'] == result['lean_toolchain'] == TOOLCHAIN and
            env['mathlib_revision'] == result['mathlib_revision'] == MATHLIB and
            (ROOT / 'lean-toolchain').read_text().strip() == TOOLCHAIN, 'Environment pins differ')
    require(set(env['executable_versions']) == {'lean', 'lake'}, 'Executable evidence missing')
    for executable, output in env['executable_versions'].items():
        require(re.match(rf'{executable}\b', output, re.I) and
                re.findall(r'\bLean\s+(?:\(\s*)?version\s+([^\s,)]+)', output, re.I) == ['4.34.1'],
                f'Wrong recorded {executable} version')
    manifest = read_json(ROOT / 'lake-manifest.json')
    require_unique([p['name'] for p in manifest['packages']], 'dependency names')
    revisions = {p['name']: p['rev'] for p in manifest['packages']}
    require(revisions.get('mathlib') == MATHLIB and env['dependency_revisions'] == revisions,
            'Locked dependency revisions disagree')
    for package in manifest['packages']:
        path = ROOT / manifest['packagesDir'] / package['name']
        require(git('-C', str(path), 'rev-parse', 'HEAD').decode().strip() == package['rev'] and
                not git('-C', str(path), 'status', '--porcelain', '--untracked-files=no').strip(),
                f'Dependency checkout changed: {package["name"]}')
    require(result['source_paper_sha256'] == digest(ROOT / 'docs/source.pdf'), 'Paper certificate differs')
    evidence.update({str(p.relative_to(ROOT)): digest(p) for p in
                     (ROOT / 'lean-toolchain', ROOT / 'lakefile.lean', ROOT / 'lake-manifest.json',
                      ROOT / 'verification/lean_upgrade/start.json', Path(__file__).resolve())})
    evidence.update({str(p.relative_to(ROOT)): digest(p) for p in
                     sorted((ROOT / 'scripts').glob('*.py'))})
    history = check_history(run_dir)
    return run, result, hashes, evidence, history, semantic_review


def archive_diagnostics(destination):
    """Select metadata files only; never traverse the preserved build/toolchain trees."""
    records = []
    selected = []
    for base in (ROOT / 'work/lean-upgrade', ROOT / 'verification/lean_upgrade'):
        selected.extend(p for suffix in ('*.json', '*.log') for p in base.glob(suffix)
                        if not p.name.startswith('completion-'))
    selected.extend(ROOT / relative for relative in
                    ('work/lean-upgrade/generic-c/readiness.json',
                     'work/lean-upgrade/cache-investigation/summary.json')
                    if (ROOT / relative).is_file())
    selected.append(Path(__file__).resolve())
    for source in sorted(set(selected)):
        require(source.is_file() and not source.is_symlink(), f'Unsafe diagnostic source: {source}')
        path = destination / source.relative_to(ROOT)
        path.parent.mkdir(parents=True, exist_ok=True)
        before = digest(source)
        shutil.copyfile(source, path)
        require(before == digest(path) == digest(source), f'Diagnostic changed while archiving: {source}')
        records.append({'source': str(source.relative_to(ROOT)),
                        'archive': str(path.relative_to(ROOT)), 'sha256': before,
                        'bytes': path.stat().st_size})
    return records


def archive_patch(destination):
    paths = ['.github/workflows/lean.yml', 'AGENTS.md', 'ASGinzburg/', 'ASGinzburg.lean',
             'AxiomAudit.lean', 'README.md', 'HANDOFF.md', 'STATUS.md', 'GAPS.md', 'RECENT_RUN.md',
             'FILES.md', 'runs/formalization-resume-20261010.md', 'lean-toolchain', 'lakefile.lean',
             'lake-manifest.json', 'scripts/', 'tests/']
    patch = git('diff', '--binary', BASELINE, '--', *paths)
    untracked = [p.decode() for p in git('ls-files', '--others', '--exclude-standard', '-z',
                                       '--', *paths).split(b'\0') if p]
    for relative in untracked:
        path = ROOT / relative
        require(path.is_file() and not path.is_symlink(), f'Unsafe untracked migration file: {relative}')
        process = subprocess.run(['git', '--no-optional-locks', 'diff', '--binary', '--no-index',
                                  '--', '/dev/null', relative], cwd=ROOT, capture_output=True)
        require(process.returncode in (0, 1), f'Could not archive new migration file: {relative}')
        patch += process.stdout
    require(patch, 'Empty migration patch')
    path = destination / 'final-migration.patch'
    path.write_bytes(patch)
    return {'archive': str(path.relative_to(ROOT)), 'sha256': digest(path),
            'bytes': len(patch), 'baseline_commit': BASELINE, 'tracked_diff_paths': paths,
            'included_untracked_files': untracked,
            'scope_note': 'Code/configuration/current documentation only; historical evidence '
                          'and verification aliases are excluded.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run-dir', type=Path, required=True)
    args = parser.parse_args()
    started, tick = datetime.now(timezone.utc).isoformat(), time.monotonic()
    run_dir = args.run_dir.resolve()
    run, result, hashes, evidence, history, semantic_review = validate(run_dir)
    output = ROOT / 'verification/lean_upgrade' / ('completion-' + run_dir.name + '.json')
    archive = output.with_suffix('')
    require(not output.exists() and not archive.exists(), 'Completion destination already exists')
    archive.mkdir(parents=True, exist_ok=False)
    records = archive_diagnostics(archive)
    patch = archive_patch(archive)
    for relative, expected in {**hashes, **evidence}.items():
        require(digest(ROOT / relative) == expected, f'Verified evidence changed during finalization: {relative}')
    require(check_history(run_dir) == history, 'Historical evidence changed during finalization')
    completion = {'status': 'upgrade_verified', 'baseline_commit': BASELINE,
                  'lean_toolchain': TOOLCHAIN, 'mathlib_revision': MATHLIB,
                  'run_id': run_dir.name, 'run_dir': str(run_dir.relative_to(ROOT)),
                  'verification_started_at_utc': run['started_at_utc'],
                  'verification_ended_at_utc': run['ended_at_utc'],
                  'verification_elapsed_seconds': run['elapsed_seconds'], 'verification_steps': run['steps'],
                  'finalization_started_at_utc': started,
                  'finalization_ended_at_utc': datetime.now(timezone.utc).isoformat(),
                  'finalization_elapsed_seconds': time.monotonic() - tick,
                  'declaration_count': DECLARATIONS, 'original_declaration_names_kinds_preserved': True,
                  'final_semantic_review': semantic_review,
                  'kernel_axiom_dependencies': result['kernel_axiom_dependencies'],
                  'historical_preservation': history, 'lean_source_sha256': hashes,
                  'verified_evidence_sha256': evidence, 'diagnostic_archives': records,
                  'final_migration_patch': patch,
                  'diagnostic_note': 'These are unmodified snapshots of intermediate records, including failures '
                                     'and static/uncompiled readiness; their original status is not changed.',
                  'prior_static_snapshot_note': 'statement-review.json precedes two explicit-P hom_ext fixes '
                                                'and is preserved as that prior static snapshot.',
                  'main_theorem_proved': result['main_theorem_proved'],
                  'scope_note': 'This certifies the pinned public library upgrade, not unpromoted drafts '
                                'or additional mathematical results.'}
    with output.open('x') as stream:
        stream.write(json.dumps(completion, indent=2) + '\n')
    print(json.dumps({'completion': str(output.relative_to(ROOT)), 'status': completion['status']}, indent=2))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError, subprocess.CalledProcessError) as error:
        print(f'Upgrade completion refused: {error}', file=sys.stderr)
        sys.exit(1)
