import datetime, hashlib, json, os, pathlib, subprocess, sys, time
root=pathlib.Path.cwd()
source=pathlib.Path(sys.argv[1]); label=sys.argv[2]
out=pathlib.Path(sys.argv[3]) if len(sys.argv)>3 else source.with_suffix('.olean')
out.parent.mkdir(parents=True,exist_ok=True)
logdir=root/'work'/'checks';logdir.mkdir(exist_ok=True)
log=logdir/(label+'.log'); ev=logdir/(label+'.json')
assert not log.exists() and not ev.exists(),label
snapshot=logdir/(label+'.lean.draft')
assert not snapshot.exists(),label
snapshot.write_bytes(source.read_bytes())
source_hash=hashlib.sha256(snapshot.read_bytes()).hexdigest()
start=datetime.datetime.now(datetime.timezone.utc).isoformat(); tick=time.monotonic()
env=os.environ.copy();env['LEAN_PATH']=env.get('LEAN_PATH','')+':'+str(root)
with log.open('w') as stream:
 p=subprocess.run(['lean','-DautoImplicit=false','-o',str(out),str(source)],stdout=stream,stderr=subprocess.STDOUT,env=env)
d={'source':str(source),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'output':str(out),'started_at_utc':start,'ended_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,'exit_code':p.returncode,'log':str(log.relative_to(root)),'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest()}
assert d['source_sha256']==source_hash
d['source_snapshot']=str(snapshot.relative_to(root))
ev.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d));print(log.read_text());sys.exit(p.returncode)
