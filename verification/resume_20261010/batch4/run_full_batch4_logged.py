from pathlib import Path
import subprocess,json,datetime,time
s=datetime.datetime.now(datetime.timezone.utc);label='full_batch4_logged_'+s.strftime('%Y%m%dT%H%M%SZ')
log=Path('work')/(label+'.log');record=Path('work')/(label+'.json')
assert not log.exists() and not record.exists()
Path('work/full_batch4_active.json').write_text(json.dumps({'label':label,'started_at_utc':s.isoformat(),'log':str(log),'record':str(record)},indent=2)+'\n')
t=time.monotonic()
with log.open('w') as out:
    p=subprocess.run(['bash','scripts/check.sh','--axiom-jobs','3'],stdout=out,stderr=subprocess.STDOUT)
record.write_text(json.dumps({'started_at_utc':s.isoformat(),'ended_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'exit_code':p.returncode,'log':str(log)},indent=2)+'\n')
print(record.read_text());raise SystemExit(p.returncode)
