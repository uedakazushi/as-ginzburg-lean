import sys,json,time,hashlib,subprocess,os
from pathlib import Path
from datetime import datetime,timezone
root=Path.cwd()
sys.path.insert(0,str(root/'scripts'))
import audit_sources,report_verification
label=sys.argv[1]
out=root/'work'/'checks'
all_paths=sorted(p for p in (root/'work'/'ASGinzburgDraft').glob('*.lean')
                 if not (root/'ASGinzburg'/p.name).exists())
paths=[root/'work'/'ASGinzburgDraft'/(n+'.lean') for n in sys.argv[2:]] if len(sys.argv)>2 else all_paths
public=audit_sources.inventory(root)
saved=audit_sources.project_sources
audit_sources.project_sources=lambda r:all_paths
all_entries=audit_sources.inventory(root)
audit_sources.project_sources=lambda r:paths
entries=audit_sources.inventory(root)
audit_sources.project_sources=saved
audit_sources.require_unique([e['name'] for e in public+all_entries],'public and draft names')
hashes={str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
source=root/'work'/f'{label}.lean'
log=out/f'{label}.log'
evidence=out/f'{label}.json'
assert not any(p.exists() for p in [source,log,evidence])
source.write_text('\n'.join('import '+str(p.relative_to(root).with_suffix('')).replace('/','.') for p in paths)
  +'\n\n'+'\n'.join('#print axioms '+e['name'] for e in entries)+'\n')
started=datetime.now(timezone.utc).isoformat(); tick=time.monotonic()
env=os.environ.copy(); env['LEAN_PATH']=env.get('LEAN_PATH','')+':'+str(root)
with log.open('w') as f:
  result=subprocess.run(['lean','-DautoImplicit=false',str(source.relative_to(root))],env=env,stdout=f,stderr=subprocess.STDOUT)
elapsed=time.monotonic()-tick; ended=datetime.now(timezone.utc).isoformat()
assert hashes=={str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
data={'started_at_utc':started,'ended_at_utc':ended,'elapsed_seconds':elapsed,
 'exit_code':result.returncode,'modules':len(paths),'declarations':len(entries),
 'source_sha256':hashes,'entries':entries,'log':str(log.relative_to(root)),
 'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),'strict_coverage':False}
if result.returncode==0:
  names,axioms=report_verification.check_coverage(entries,log.read_text())
  data.update(strict_coverage=True,unique_declarations=len(names),axioms=sorted(axioms))
evidence.write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps({k:v for k,v in data.items() if k not in ['source_sha256','entries']}),flush=True)
if result.returncode: print(log.read_text())
sys.exit(result.returncode)
