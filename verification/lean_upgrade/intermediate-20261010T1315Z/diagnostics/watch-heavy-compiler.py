"""Guard only the known runaway reciprocity compiler during diagnostics."""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import signal
import time

source = Path('ASGinzburg/ASLeftExtReciprocity.lean')
folder = Path('work/lean-upgrade')
stop = folder / 'stop-reciprocity-memory-watch'
assert not stop.exists()
limit = 8 * 1024**3
started = time.monotonic()
signalled = set()
print('Watching only ASLeftExtReciprocity diagnostic Lean processes, RSS limit8GiB.', flush=True)
while time.monotonic() - started < 3600 and not stop.exists():
    for proc in Path('/proc').iterdir():
        if not proc.name.isdecimal() or int(proc.name) in signalled:
            continue
        try:
            args = [a.decode() for a in (proc / 'cmdline').read_bytes().split(b'\0') if a]
            if not args or Path(args[0]).name != 'lean':
                continue
            if str(source) not in args and str(source.resolve()) not in args:
                continue
            rss = int((proc / 'statm').read_text().split()[1]) * os.sysconf('SC_PAGE_SIZE')
            if rss < limit:
                continue
            pid = int(proc.name)
            record = folder / f'ASLeftExtReciprocity-memory-guard-pid{pid}.json'
            assert not record.exists()
            data = {'observed_at_utc': datetime.now(timezone.utc).isoformat(),
                    'pid': pid, 'source': str(source),
                    'source_sha256_at_guard': hashlib.sha256(source.read_bytes()).hexdigest(),
                    'observed_rss_bytes': rss, 'rss_limit_bytes': limit,
                    'cgroup_memory_current_bytes': int(Path('/sys/fs/cgroup/memory.current').read_text()),
                    'signal': 'SIGTERM', 'reason': 'Known diagnostic inference runaway exceeds8GiB RSS',
                    'global_build_success': False}
            os.kill(pid, signal.SIGTERM)
            data['signal_sent_at_utc'] = datetime.now(timezone.utc).isoformat()
            record.write_text(json.dumps(data, indent=2) + '\n')
            signalled.add(pid)
            print(json.dumps(data), flush=True)
        except (FileNotFoundError, ProcessLookupError, PermissionError, IndexError):
            continue
    time.sleep(0.5)
print('Memory watch ended.', flush=True)
