"""Build only frozen targets with actual current default compiler passes."""
import datetime, hashlib, json, pathlib, subprocess, sys
folder=pathlib.Path('work/lean-upgrade')
label=sys.argv[1]
sources=sys.argv[2:]
assert sources and len(sources)==len(set(sources))
records={}
for p in folder.glob('*.json'):
 try: data=json.loads(p.read_text())
 except ValueError: continue
 if not isinstance(data,dict) or data.get('exit_code') != 0: continue
 cmd=data.get('command', [])
 if not isinstance(cmd,list) or cmd[:-1] != ['bash','scripts/with_lean.sh','lake','env','lean','-DautoImplicit=false']: continue
 if data.get('source_unchanged') and 'source' in data:
  source,sha=data['source'],data.get('source_sha256')
 elif data.get('source_sha256_before')==data.get('source_sha256_after') and data.get('source_sha256_after'):
  source,sha=cmd[-1],data['source_sha256_after']
 else: continue
 if source in sources and hashlib.sha256(pathlib.Path(source).read_bytes()).hexdigest()==sha:
  records[source]=str(p)
assert set(records)==set(sources), f'Missing actual current direct passes: {set(sources)-set(records)}'
meta=folder/(label+'-source-start.json')
assert not meta.exists()
meta.write_text(json.dumps({'recorded_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'sources':sources, 'source_sha256':{s:hashlib.sha256(pathlib.Path(s).read_bytes()).hexdigest() for s in sources},
 'current_default_exit_zero_records':records,'full_build_certificate':False},indent=2)+'\n')
cmd=[sys.executable,str(folder/'run-timed.py'),label,'bash','scripts/with_lean.sh','lake','build',*[s[:-5].replace('/','.') for s in sources]]
code=subprocess.call(cmd)
assert all(hashlib.sha256(pathlib.Path(s).read_bytes()).hexdigest()==json.loads(meta.read_text())['source_sha256'][s] for s in sources), 'Source changed during narrow build'
sys.exit(code)
