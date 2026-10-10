"""Capture a task command's real exit status, UTC times and elapsed seconds."""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

label, *command = sys.argv[1:]
if not re.fullmatch(r'[A-Za-z0-9_-]+', label) or not command:
    raise ValueError('Expected a simple label and a command')
directory = Path('work/lean-upgrade')
log = directory / (label + '.log')
record = directory / (label + '.json')
if log.exists() or record.exists():
    raise FileExistsError(label)
env = os.environ.copy()
env['AS_GINZBURG_LEAN_ROOT'] = str(Path.cwd() / directory / 'lean-4.34.1-linux')
env['AS_GINZBURG_PROC_SELF_FIX'] = '1'
started = datetime.now(timezone.utc).isoformat(timespec='microseconds')
tick = time.monotonic()
with log.open('w') as stream:
    process = subprocess.run(command, env=env, stdout=stream, stderr=subprocess.STDOUT)
result = {'command': command, 'started_at_utc': started,
          'ended_at_utc': datetime.now(timezone.utc).isoformat(timespec='microseconds'),
          'elapsed_seconds': time.monotonic() - tick, 'exit_code': process.returncode,
          'lean_root': env['AS_GINZBURG_LEAN_ROOT'], 'log': str(log),
          'log_sha256': hashlib.sha256(log.read_bytes()).hexdigest()}
record.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2), flush=True)
sys.exit(process.returncode if process.returncode >= 0 else 1)
