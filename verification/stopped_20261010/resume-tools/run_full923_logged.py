from pathlib import Path
import subprocess,json,datetime,time
root=Path.cwd();s=datetime.datetime.now(datetime.timezone.utc)
label='full923_logged_'+s.strftime('%Y%m%dT%H%M%SZ')
log=root/'work'/(label+'.log');record=root/'work'/(label+'.json')
assert not log.exists() and not record.exists()
(root/'work'/'full923_active.json').write_text(json.dumps({'label':label,'started_at_utc':s.isoformat(),'log':str(log.relative_to(root)),'record':str(record.relative_to(root))},indent=2)+'\n')
t=time.monotonic()
with log.open('w') as out:
    p=subprocess.run(['bash','scripts/check.sh','--axiom-jobs','3'],stdout=out,stderr=subprocess.STDOUT)
record.write_text(json.dumps({'started_at_utc':s.isoformat(),'ended_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'exit_code':p.returncode,'log':str(log.relative_to(root))},indent=2)+'\n')
print(record.read_text());raise SystemExit(p.returncode)
