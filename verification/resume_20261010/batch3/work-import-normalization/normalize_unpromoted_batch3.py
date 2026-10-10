from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,re,shutil
root=Path.cwd()
run=json.loads((root/'verification/runs/20261010T043623Z-ba37043f/run.json').read_text())
assert next(s for s in run['steps'] if s['stage']=='build')['exit_code']==0
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert all(sha(root/p)==h for p,h in run['lean_source_sha256'].items())
now=datetime.now(timezone.utc);out=root/'verification/resume_20261010/batch3/work-import-normalization'
assert not out.exists();(out/'before').mkdir(parents=True);(out/'after').mkdir()
checks=[]
for p in (root/'work/checks').glob('*.json'):
 try:checks.append(json.loads(p.read_text()))
 except json.JSONDecodeError:pass
entries=[]
for p in sorted((root/'work/ASGinzburgDraft').glob('*.lean')):
 if (root/'ASGinzburg'/p.name).exists():continue
 oldsha=sha(p);old=p.read_text();new=old
 for dep in re.findall(r'^import work\.ASGinzburgDraft\.([A-Za-z0-9_]+)$',old,re.M):
  if (root/'ASGinzburg'/(dep+'.lean')).exists():
   new=new.replace('import work.ASGinzburgDraft.'+dep+'\n','import ASGinzburg.'+dep+'\n')
 clean=any(d.get('exit_code')==0 and d.get('source')==str(p.relative_to(root)) and
   d.get('source_sha256')==oldsha and d.get('log_sha256')==hashlib.sha256(b'').hexdigest() for d in checks)
 shutil.copy2(p,out/'before'/p.name)
 p.write_text(new);shutil.copy2(p,out/'after'/p.name)
 entries.append({'name':p.stem,'source':str(p.relative_to(root)),'before_sha256':oldsha,
  'after_sha256':sha(p),'changed':old!=new,'previous_current_clean_check':clean})
assert all(sha(root/p)==h for p,h in run['lean_source_sha256'].items())
record={'normalized_at_utc':now.isoformat(),'public_build_exit_code':0,'public_sources_unchanged':True,
 'all_agents_paused_before_mutation':True,'entries':entries,'rechecks':'pending; previous source checks are historical'}
(out/'normalization.json').write_text(json.dumps(record,indent=2)+'\n')
shutil.copy2(root/'work/normalize_unpromoted_batch3.py',out/'normalize_unpromoted_batch3.py')
print(json.dumps({'drafts':len(entries),'changed':sum(e['changed'] for e in entries),
 'previous_clean':sum(e['previous_current_clean_check'] for e in entries),'public_sources_unchanged':True}))
