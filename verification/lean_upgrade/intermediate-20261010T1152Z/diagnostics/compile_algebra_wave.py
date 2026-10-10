from pathlib import Path
from datetime import datetime,timezone
import subprocess,os,json,time,hashlib,sys
out=Path('work/lean-upgrade');env=os.environ.copy();env['AS_GINZBURG_LEAN_ROOT']=str((out/'lean-4.34.1-linux').resolve());env['AS_GINZBURG_PROC_SELF_FIX']='1'
for stem in sys.argv[2:]:
 source=Path('ASGinzburg')/(stem+'.lean');name=stem+'-compile-'+sys.argv[1];cmd=['bash','scripts/with_lean.sh','lake','env','lean','-DautoImplicit=false',str(source)]
 if (out/(name+'.json')).exists():raise ValueError('Refuse to overwrite historical check '+name)
 start=datetime.now(timezone.utc).isoformat();mono=time.monotonic();sha=hashlib.sha256(source.read_bytes()).hexdigest()
 with (out/(name+'.log')).open('w') as log:p=subprocess.run(cmd,env=env,stdout=log,stderr=subprocess.STDOUT)
 record={'command':cmd,'start_utc':start,'end_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-mono,'exit_code':p.returncode,'source_sha256_before':sha,'source_sha256_after':hashlib.sha256(source.read_bytes()).hexdigest(),'log_sha256':hashlib.sha256((out/(name+'.log')).read_bytes()).hexdigest()}
 (out/(name+'.json')).write_text(json.dumps(record,indent=2)+'\n')
 print(json.dumps({'module':stem,'exit_code':p.returncode,'elapsed_seconds':record['elapsed_seconds'],'json':str(out/(name+'.json'))}),flush=True)
 if p.returncode:print((out/(name+'.log')).read_text(),flush=True)
