from pathlib import Path
import datetime,hashlib,json,os,subprocess,sys,time
source=Path(sys.argv[1]);label=sys.argv[2];outdir=Path('work/lean-upgrade')
log=outdir/(label+'.log');record=outdir/(label+'.json');snapshot=outdir/(label+'.lean.source')
assert not any(p.exists() for p in [log,record,snapshot]),label
snapshot.write_bytes(source.read_bytes());sha=hashlib.sha256(snapshot.read_bytes()).hexdigest()
env=os.environ.copy();env['AS_GINZBURG_LEAN_ROOT']=str(Path.cwd()/'work/lean-upgrade/lean-4.34.1-linux');env['AS_GINZBURG_PROC_SELF_FIX']='1'
cmd=['bash','scripts/with_lean.sh','lake','env','lean','-DautoImplicit=false',str(source)]
started=datetime.datetime.now(datetime.timezone.utc).isoformat();tick=time.monotonic()
with log.open('w') as stream:
 p=subprocess.run(cmd,env=env,stdout=stream,stderr=subprocess.STDOUT)
result={'command':cmd,'source':str(source),'source_sha256':sha,'source_unchanged':hashlib.sha256(source.read_bytes()).hexdigest()==sha,'source_snapshot':str(snapshot),'started_at_utc':started,'finished_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,'exit_code':p.returncode,'log':str(log),'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),'wrote_olean':False}
record.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result));print(log.read_text());sys.exit(p.returncode)
