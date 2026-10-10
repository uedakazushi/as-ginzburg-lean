"""Record and stop only a project build compiler approaching the memory limit."""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import signal
import sys
import time

folder = Path('work/lean-upgrade')
label = sys.argv[1]
owner_checks = len(sys.argv) > 2 and sys.argv[2] == 'owner-checks'
rss_limit = (8 if owner_checks else 10) * 1024**3
output = folder / (label + '-memory-guard.json')
closed = folder / (label + '.json')
assert not output.exists() and not closed.exists()
started = datetime.now(timezone.utc).isoformat()
interventions = []
signalled = set()
while not closed.exists():
    memory = int(Path('/sys/fs/cgroup/memory.current').read_text())
    candidates = []
    for p in Path('/proc').iterdir():
        if not p.name.isdigit():
            continue
        try:
            if (p / 'comm').read_text().strip() != 'lean':
                continue
            argv = (p / 'cmdline').read_bytes().decode().split('\0')
            if '--setup' not in argv and not owner_checks:
                continue  # Excludes all direct checks and axiom audit processes.
            sources = [str(Path(s).resolve()) for s in argv if s.endswith('.lean') and
                       (str(Path(s).resolve()).startswith(str(Path.cwd() / 'ASGinzburg')) or
                        (owner_checks and str(Path(s).resolve()).startswith(str(Path.cwd() / 'work/lean-upgrade'))))]
            if len(sources) != 1:
                continue
            rss = next(int(s.split()[1]) * 1024 for s in (p / 'status').read_text().splitlines() if s.startswith('VmRSS:'))
            candidates.append((rss, int(p.name), sources[0], argv))
        except (OSError, StopIteration, ValueError):
            continue
    if candidates:
        rss, pid, source, argv = max(candidates)
        if pid not in signalled and (rss > rss_limit or memory > 14 * 1024**3):
            event = {'utc': datetime.now(timezone.utc).isoformat(), 'pid': pid,
                     'command': argv, 'source': source,
                     'source_sha256': hashlib.sha256(Path(source).read_bytes()).hexdigest(),
                     'rss_bytes': rss, 'cgroup_memory_current_bytes': memory,
                     'signal': 'SIGTERM', 'successful_compile': False,
                     'reason': 'Prevent a repeat of observed OOM termination; this is a resource interruption, not a mathematical counterexample.'}
            try:
                os.kill(pid, signal.SIGTERM)
            except ProcessLookupError:
                continue
            signalled.add(pid)
            target = folder / (label + '-memory-intervention-' + str(pid) + '.json')
            assert not target.exists()
            target.write_text(json.dumps(event, indent=2) + '\n')
            interventions.append(str(target))
    time.sleep(1)
output.write_text(json.dumps({'started_at_utc': started,
    'ended_at_utc': datetime.now(timezone.utc).isoformat(),
    'rss_limit_bytes': rss_limit, 'cgroup_limit_bytes': 14 * 1024**3,
    'owner_direct_checks_included': owner_checks,
    'intervention_records': interventions, 'proof_limits_changed': False,
    'closed_build_record': str(closed), 'full_verification_complete': False}, indent=2) + '\n')
print(output.read_text())
