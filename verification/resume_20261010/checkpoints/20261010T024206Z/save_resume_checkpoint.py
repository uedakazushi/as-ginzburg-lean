from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,shutil,time
root=Path.cwd();now=datetime.now(timezone.utc);label=now.strftime('%Y%m%dT%H%M%SZ')
out=root/'verification/resume_20261010/checkpoints'/label
assert not out.exists();(out/'drafts').mkdir(parents=True);(out/'checks').mkdir()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
checks=[]
for p in sorted((root/'work/checks').glob('*')):
 if p.is_file():
  shutil.copy2(p,out/'checks'/p.name)
  if p.suffix=='.json':
   try: checks.append((p,json.loads(p.read_text())))
   except json.JSONDecodeError: pass
entries=[]
for p in sorted((root/'work/ASGinzburgDraft').glob('*.lean')):
 if (root/'ASGinzburg'/p.name).exists():continue
 data=p.read_bytes();h=hashlib.sha256(data).hexdigest();dest=out/'drafts'/p.name;dest.write_bytes(data)
 valid=[str(q.relative_to(root)) for q,d in checks if d.get('exit_code')==0
     and d.get('source')==str(p.relative_to(root)) and d.get('source_sha256')==h
     and (root/d.get('log','')).is_file() and sha(root/d['log'])==d.get('log_sha256')]
 entries.append({'source':str(p.relative_to(root)),'source_sha256':h,'snapshot':str(dest.relative_to(root)),
    'current_sha_individual_checks':valid,'public_full_run_scope':False})
run=json.loads((root/'verification/runs/20261010T020006Z-65de0cea/run.json').read_text())
start=json.loads((root/'work/resume_start.json').read_text())
state={'checkpoint_at_utc':now.isoformat(),'purpose':'ongoing mathematical continuation checkpoint; not task termination',
 'public_full_run':{'run_id':run['run_id'],'status':run['status'],'stages':[(s['stage'],s.get('exit_code')) for s in run['steps']]},
 'unpromoted_drafts':entries,'current_sha_individual_successes':sum(bool(e['current_sha_individual_checks']) for e in entries),
 'github_actions_started':False,'main_save_pending_full_success':run['status']!='success'}
(out/'state.json').write_text(json.dumps(state,indent=2)+'\n')
(out/'session-progress.json').write_text(json.dumps({'started_at_utc':start['started_at_utc'],'checkpoint_at_utc':now.isoformat(),
 'elapsed_seconds':time.monotonic()-start['monotonic'],'continuation_active':True},indent=2)+'\n')
shutil.copy2(root/'work/save_resume_checkpoint.py',out/'save_resume_checkpoint.py')
print(json.dumps({'checkpoint':str(out.relative_to(root)),'drafts':len(entries),'current_sha_individual_successes':state['current_sha_individual_successes'],'public_full_run':state['public_full_run']}))
