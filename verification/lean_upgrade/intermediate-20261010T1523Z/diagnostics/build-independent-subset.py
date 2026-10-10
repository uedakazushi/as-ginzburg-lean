"""Build the exact graph slice independent of the resource-heavy diagnostic leaf."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

label = sys.argv[1]
folder = Path('work/lean-upgrade')
record = folder / (label + '-source-start.json')
result = folder / (label + '-source-end.json')
assert not record.exists() and not result.exists()
paths = {'ASGinzburg.' + p.stem: p for p in Path('ASGinzburg').glob('*.lean')}
imports = {m: re.findall(r'^import\s+(ASGinzburg\.\S+)', p.read_text(), re.M)
           for m, p in paths.items()}
blocked = set(sys.argv[2:] or ['ASGinzburg.ASLeftExtReciprocity'])
assert blocked <= paths.keys(), 'Unknown excluded project module'
excluded_seeds = sorted(blocked)
while True:
    more = {m for m, dependencies in imports.items()
            if any(dependency in blocked for dependency in dependencies)} - blocked
    if not more:
        break
    blocked |= more
unbuilt = {m for m, p in paths.items()
           if not (Path('.lake/build/lib/lean') / p).with_suffix('.olean').is_file()}
independent = unbuilt - blocked
roots = sorted(independent - {i for m in independent for i in imports[m]
                              if i in independent})
assert roots
sources = [Path('ASGinzburg.lean'), *sorted(Path('ASGinzburg').glob('*.lean'))]
before = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
record.write_text(json.dumps({
    'recorded_at_utc': datetime.now(timezone.utc).isoformat(),
    'purpose': 'Partial diagnostic graph slice; not a full build certificate',
    'excluded_seed_modules': excluded_seeds,
    'excluded_leaf_and_transitive_dependents': sorted(blocked),
    'unbuilt_independent_modules': sorted(independent), 'targets': roots,
    'source_sha256': before, 'global_build_success': False,
}, indent=2) + '\n')
code = subprocess.call([sys.executable, str(folder / 'run-timed.py'), label,
                        'env', 'LEAN_NUM_THREADS=1', 'bash', 'scripts/with_lean.sh', 'lake', 'build', *roots])
after = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
result.write_text(json.dumps({
    'recorded_at_utc': datetime.now(timezone.utc).isoformat(),
    'exit_code': code, 'all_public_sources_unchanged': before == after,
    'changed_sources': [p for p in before if before[p] != after[p]],
    'global_build_success': False,
}, indent=2) + '\n')
assert before == after, 'Public sources changed during diagnostic build'
sys.exit(code)
