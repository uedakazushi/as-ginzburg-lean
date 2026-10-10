import sys,os,subprocess,json,time,datetime,re
from pathlib import Path
sys.path.insert(0,'scripts')
from audit_sources import project_sources,ROOT
imports=sorted({n for p in project_sources(ROOT)+list(Path('work/ASGinzburgDraft').glob('*.lean')) for n in re.findall(r'^import (Mathlib\.\S+)',p.read_text(),re.M)})
start=datetime.datetime.now(datetime.timezone.utc).isoformat();tick=time.monotonic()
command=['bash','scripts/with_lean.sh','lake','env','.lake/packages/mathlib/.lake/build/bin/cache','get',*imports]
with open('work/resume-cache.log','w') as f: code=subprocess.call(command,stdout=f,stderr=subprocess.STDOUT)
data={'command':command,'started_at_utc':start,'ended_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,'exit_code':code}
Path('work/resume-cache.json').write_text(json.dumps(data,indent=2)+'\n');print(json.dumps(data));sys.exit(code)
