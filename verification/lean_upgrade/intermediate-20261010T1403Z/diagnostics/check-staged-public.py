"""Check the staged public blobs against the reviewed checkpoint in one batch."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

checkpoint = Path(sys.argv[1]) / 'checkpoint.json'
output = Path(sys.argv[2])
assert not output.exists()
started, begin = datetime.now(timezone.utc).isoformat(), time.monotonic()
expected = json.loads(checkpoint.read_text())['public_source_sha256']
assert len(expected) == 1373
index = {}
for line in subprocess.check_output(['git', 'ls-files', '--stage', '-z']).split(b'\0'):
    if not line:
        continue
    metadata, path = line.split(b'\t', 1)
    mode, blob, stage = metadata.decode().split()
    index[path.decode()] = (mode, blob, stage)
paths = sorted(expected)
raw_hashes = subprocess.check_output(
    ['git', 'hash-object', '--no-filters', '--stdin-paths'],
    input=('\n'.join(paths) + '\n').encode()).decode().splitlines()
assert len(raw_hashes) == len(paths)
for path, blob in zip(paths, raw_hashes):
    assert hashlib.sha256(Path(path).read_bytes()).hexdigest() == expected[path], path
    assert index[path] == ('100644', blob, '0'), path
output.write_text(json.dumps({
    'started_at_utc': started, 'ended_at_utc': datetime.now(timezone.utc).isoformat(),
    'elapsed_seconds': time.monotonic() - begin, 'exit_code': 0,
    'checkpoint': str(checkpoint),
    'checkpoint_sha256': hashlib.sha256(checkpoint.read_bytes()).hexdigest(),
    'public_sources_checked': len(paths), 'reviewed_source_sha256_matches': True,
    'git_staged_raw_blobs_and_modes_match_current_reviewed_sources': True,
}, indent=2) + '\n')
print(output.read_text())
