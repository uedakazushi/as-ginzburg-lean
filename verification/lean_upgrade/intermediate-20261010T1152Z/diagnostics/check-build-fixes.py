"""Read actual direct-compiler evidence; optionally snapshot a diagnostic build."""
from pathlib import Path
import datetime
import hashlib
import json
import sys

stage = sys.argv[1]
folder = Path('work/lean-upgrade')
log = (folder / (stage + '.log')).read_text()
tail = log[log.index('Some required targets logged failures:'):]
failed = [line[2:].replace('.', '/') + '.lean'
          for line in tail.splitlines() if line.startswith('- ')]
passed = {}
for path in folder.glob('*.json'):
    try:
        data = json.loads(path.read_text())
    except ValueError:
        continue
    if not isinstance(data, dict) or data.get('exit_code') != 0:
        continue
    if data.get('source_unchanged') and 'source' in data:
        source, sha = data['source'], data.get('source_sha256')
    elif (data.get('source_sha256_before') == data.get('source_sha256_after')
          and data.get('source_sha256_after') and isinstance(data.get('command'), list)):
        source, sha = data['command'][-1], data['source_sha256_after']
    else:
        continue
    if Path(source).exists() and hashlib.sha256(Path(source).read_bytes()).hexdigest() == sha:
        passed[source] = str(path)
missing = [source for source in failed if source not in passed]
print(json.dumps({'diagnostic': stage, 'failed_leaves': len(failed),
                  'current_direct_passed': len(failed) - len(missing), 'pending': missing}))
if len(sys.argv) == 3:
    if missing:
        sys.exit(2)
    now = datetime.datetime.now(datetime.timezone.utc).isoformat()
    ready = folder / (stage + '-leaves-ready.json')
    snapshot = folder / (sys.argv[2] + '-source-start.json')
    if ready.exists() or snapshot.exists():
        raise FileExistsError('Diagnostic evidence must be fresh')
    ready.write_text(json.dumps({'recorded_at_utc': now, 'diagnostic_failed_leaves': failed,
        'all_current_sources_have_direct_exit_zero': True,
        'records': {source: passed[source] for source in failed},
        'global_build_success': False}, indent=2) + '\n')
    sources = [Path('ASGinzburg.lean'), *sorted(Path('ASGinzburg').rglob('*.lean'))]
    snapshot.write_text(json.dumps({'recorded_at_utc': now,
        'source_sha256': {str(source): hashlib.sha256(source.read_bytes()).hexdigest()
                          for source in sources},
        'toolchain': 'leanprover/lean4:v4.34.1',
        'purpose': 'Diagnostic full build; not a final verification certificate'}, indent=2) + '\n')
