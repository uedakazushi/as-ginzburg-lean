"""Observe actual compiler concurrency and cgroup memory for a timed build."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys
import time

folder = Path('work/lean-upgrade')
label = sys.argv[1]
output = folder / (label + '-resources.json')
closed = folder / (label + '.json')
assert not output.exists() and not closed.exists()
started = datetime.now(timezone.utc).isoformat()
events = Path('/sys/fs/cgroup/memory.events')
before = events.read_text()
samples = []
while True:
    lean = []
    for p in Path('/proc').iterdir():
        if not p.name.isdigit():
            continue
        try:
            if (p / 'comm').read_text().strip() != 'lean':
                continue
            command = (p / 'cmdline').read_bytes().replace(b'\0', b' ').decode(errors='replace').strip()
            status = (p / 'status').read_text().splitlines()
            rss = next(int(s.split()[1]) * 1024 for s in status if s.startswith('VmRSS:'))
            lean.append({'pid': int(p.name), 'rss_bytes': rss, 'command': command})
        except (OSError, StopIteration, ValueError):
            continue
    samples.append({'utc': datetime.now(timezone.utc).isoformat(), 'lean_processes': lean,
                    'cgroup_memory_current_bytes': int(Path('/sys/fs/cgroup/memory.current').read_text())})
    if closed.exists():
        break
    time.sleep(3)
build = json.loads(closed.read_text())
output.write_text(json.dumps({
    'started_at_utc': started, 'ended_at_utc': datetime.now(timezone.utc).isoformat(),
    'closed_build_record': str(closed),
    'closed_build_record_sha256': hashlib.sha256(closed.read_bytes()).hexdigest(),
    'actual_build_exit_code': build['exit_code'],
    'sampling_interval_seconds': 3, 'observed_max_simultaneous_lean_processes': max(len(s['lean_processes']) for s in samples),
    'process_identification': '/proc/<pid>/comm equals lean; cmdline and RSS recorded; exe symlink is permission restricted',
    'observed_peak_cgroup_memory_bytes': max(s['cgroup_memory_current_bytes'] for s in samples),
    'memory_events_before': before, 'memory_events_after': events.read_text(),
    'samples': samples, 'does_not_change_proof_limits_or_terminate_processes': True,
    'full_verification_complete': False,
}, indent=2) + '\n')
print(output.read_text()[:1500])
