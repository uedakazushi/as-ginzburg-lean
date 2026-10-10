"""Bind a closed diagnostic build to its unchanged public source snapshot."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys

folder = Path('work/lean-upgrade')
label = sys.argv[1]
start_path = folder / (label + '-source-start.json')
build_path = folder / (label + '.json')
output = folder / (label + '-source-end.json')
assert not output.exists()
start = json.loads(start_path.read_text())
build = json.loads(build_path.read_text())
expected = start['source_sha256']
assert len(expected) == 1373
assert build['exit_code'] in (0, 1) or build['exit_code'] < 0
assert hashlib.sha256(Path(build['log']).read_bytes()).hexdigest() == build['log_sha256']
changed = [p for p, digest in expected.items()
           if hashlib.sha256(Path(p).read_bytes()).hexdigest() != digest]
output.write_text(json.dumps({
    'recorded_at_utc': datetime.now(timezone.utc).isoformat(),
    'source_start_record': str(start_path),
    'source_start_record_sha256': hashlib.sha256(start_path.read_bytes()).hexdigest(),
    'closed_build_record': str(build_path),
    'closed_build_record_sha256': hashlib.sha256(build_path.read_bytes()).hexdigest(),
    'build_exit_code': build['exit_code'], 'public_sources_checked': len(expected),
    'build_interrupted': build['exit_code'] < 0,
    'all_public_sources_unchanged': not changed, 'changed_sources': changed,
    'exhaustive_axiom_audit_complete': False, 'full_verification_complete': False,
}, indent=2) + '\n')
assert not changed, 'Public sources changed during build'
print(output.read_text())
