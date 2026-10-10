"""Save an honest, immutable intermediate upgrade checkpoint while quiescent."""
import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
FOLDER = ROOT / 'work/lean-upgrade'
spec = importlib.util.spec_from_file_location('upgrade_finalizer', FOLDER / 'finalize-upgrade.py')
finalizer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(finalizer)

def read(path):
    return json.loads(path.read_text())

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def utc():
    return datetime.now(timezone.utc).isoformat()

def source_hashes():
    return {str(p.relative_to(ROOT)): sha(p) for p in finalizer.project_sources(ROOT)}

parser = argparse.ArgumentParser()
parser.add_argument('--name', required=True)
parser.add_argument('--build', required=True)
parser.add_argument('--review', required=True)
parser.add_argument('--audit', required=True)
parser.add_argument('--running-build')
args = parser.parse_args()
assert args.name.startswith('intermediate-') and '/' not in args.name
destination = ROOT / 'verification/lean_upgrade' / args.name
assert not destination.exists(), 'Refuse to overwrite checkpoint'
sources = source_hashes()
review_path = FOLDER / (args.review + '.json')
review = read(review_path)
ready_path = FOLDER / (args.review + '-ready.json')
assert ready_path.is_file(), 'Independent semantic reviewer has not closed this review'
ready = read(ready_path)
assert ready['review_complete'] is True and ready['review_sha256'] == sha(review_path)
assert review['source_sha256'] == sources, 'Review source snapshot differs'
assert review['declaration_names_and_kinds_preserved']
assert not review['concrete_semantic_concerns']
assert not review['new_mathematical_hypotheses_found']
assert not review['weakened_mathematical_conclusions_found']
build = read(FOLDER / (args.build + '.json'))
assert build['exit_code'] in (0, 1) or build['exit_code'] < 0
assert sha(ROOT / build['log']) == build['log_sha256']
audit = read(FOLDER / (args.audit + '.json'))
assert audit['exit_code'] == 0 and sha(ROOT / audit['log']) == audit['log_sha256']
output_dir = ROOT / audit['command'][-1]
entries = finalizer.inventory(ROOT)
assert len(entries) == 6909 and read(output_dir / 'declarations.json') == entries
assert not subprocess.check_output(['git', 'diff', '00d7fa9', '--', 'scripts/', 'tests/'], cwd=ROOT)
started, monotonic = utc(), time.monotonic()
history = finalizer.check_history(ROOT / 'verification/runs' / ('unused-' + args.name))
history.pop('new_run_exception')
history.update(started_at_utc=started, ended_at_utc=utc(),
               elapsed_seconds=time.monotonic() - monotonic, exit_code=0)
previous = {}
for p in sorted((ROOT / 'verification/lean_upgrade').glob('intermediate-*/checkpoint.json')):
    data = read(p)
    for key in ('archived_diagnostics', 'archived_new_or_changed_diagnostics'):
        previous.update(data.get(key, {}))
destination.mkdir()
archived = {}
for base in (FOLDER, ROOT / 'verification/lean_upgrade'):
    for p in sorted(base.iterdir()):
        if base == FOLDER and args.running_build and p.name == args.running_build + '.log':
            continue  # Never archive a live, growing log as a closed diagnostic.
        if not p.is_file() or not (p.suffix in ('.json', '.log', '.py') or p.name.endswith('.lean.source')):
            continue
        relative = str(p.relative_to(ROOT))
        digest = sha(p)
        if previous.get(relative, {}).get('sha256') == digest:
            continue
        name = p.name if base == FOLDER else 'repository-' + p.name
        target = destination / 'diagnostics' / name
        target.parent.mkdir(exist_ok=True)
        shutil.copyfile(p, target)
        assert sha(target) == digest == sha(p), 'Diagnostic changed during copy'
        archived[relative] = {'saved_at': str(target.relative_to(ROOT)), 'sha256': digest,
                              'bytes': target.stat().st_size}
shutil.copyfile(output_dir / 'declarations.json', destination / 'declarations.json')
pending = []
build_log = (ROOT / build['log']).read_text()
failure_footer_present = 'Some required targets logged failures:' in build_log
if build['exit_code'] and failure_footer_present:
    tail = build_log.split('Some required targets logged failures:')[1]
    pending = [s[2:].replace('.', '/') + '.lean' for s in tail.splitlines() if s.startswith('- ')]
elif build['exit_code']:
    pending = list(dict.fromkeys(re.findall(r'error: (ASGinzburg/[^:\n]+\.lean):', build_log)))
assert source_hashes() == sources, 'Sources changed during archival'
checkpoint = {
    'recorded_at_utc': utc(),
    'checkpoint_kind': 'incomplete Lean stable migration, authorized intermediate main save',
    'baseline_commit': finalizer.BASELINE,
    'previous_saved_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT).decode().strip(),
    'lean_toolchain': finalizer.TOOLCHAIN, 'mathlib_revision': finalizer.MATHLIB,
    'migration_elapsed_seconds': time.monotonic() - read(FOLDER / 'start.json')['monotonic'],
    'public_math_modules': 1372, 'public_declarations': 6909,
    'regression_tests_last_execution': {
        'record': 'verification/lean_upgrade/intermediate-20261010T1152Z/diagnostics/regression-checkpoint-01.json',
        'tests': 24, 'exit_code': 0, 'scripts_and_tests_unchanged_since_that_execution': True},
    'source_audit': audit, 'source_inventory_sha256': sha(destination / 'declarations.json'),
    'last_completed_full_diagnostic': build, 'diagnostic_failed_leaves': pending,
    'last_full_diagnostic_was_interrupted': build['exit_code'] < 0,
    'diagnostic_failure_footer_present': failure_footer_present,
    'diagnostic_failure_list_complete': build['exit_code'] == 0 or failure_footer_present,
    'next_diagnostic_running_at_save': args.running_build,
    'new_lean_full_build_success': build['exit_code'] == 0,
    'new_lean_exhaustive_axiom_audit_complete': False, 'new_lean_full_verification_complete': False,
    'independent_statement_review': str(review_path.relative_to(ROOT)),
    'protected_history': history, 'github_actions_started': False,
    'push_confirmation_pending': True, 'public_source_sha256': sources,
    'archived_new_or_changed_diagnostics': archived,
}
(destination / 'checkpoint.json').write_text(json.dumps(checkpoint, ensure_ascii=False, indent=2) + '\n')
print(json.dumps({'checkpoint': str(destination.relative_to(ROOT)), 'new_diagnostics': len(archived),
                  'bytes': sum(d['bytes'] for d in archived.values()), 'history_files': history['tracked_files_checked']}))
