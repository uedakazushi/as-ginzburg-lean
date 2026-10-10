from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,re,shutil,sys,subprocess
root=Path.cwd();sys.path.insert(0,str(root/'scripts'));import audit_sources
ready=json.loads((root/'work/ready_batch4_candidate1.json').read_text())['ready']
audit=json.loads((root/'work/checks/resume-next-public-batch4-combined-audit-1.json').read_text())
assert audit['exit_code']==0 and audit['strict_coverage'] and audit['modules']==len(ready)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert len(ready)==121
assert audit['source_sha256']=={e['source']:e['sha256'] for e in ready.values()}
old=json.loads((root/'verification/runs/20261010T043623Z-ba37043f/run.json').read_text())
assert old['status']=='success' and all(sha(root/n)==h for n,h in old['lean_source_sha256'].items())
out=root/'verification/resume_20261010/batch4';assert not out.exists();(out/'drafts').mkdir(parents=True);(out/'checks').mkdir()
entries=[]
for name,e in ready.items():
 src=root/e['source'];dst=root/'ASGinzburg'/(name+'.lean');assert not dst.exists() and sha(src)==e['sha256']
 shutil.copy2(src,out/'drafts'/src.name)
 text=src.read_text()
 for dep in re.findall(r'^import work\.ASGinzburgDraft\.([A-Za-z0-9_]+)$',text,re.M):
  assert dep in ready or (root/'ASGinzburg'/(dep+'.lean')).exists(),(name,dep)
 text=text.replace('import work.ASGinzburgDraft.','import ASGinzburg.')
 dst.write_text(text)
 entries.append({'draft':e['source'],'draft_sha256':e['sha256'],'public':str(dst.relative_to(root)),'public_sha256':sha(dst)})
for p in (root/'work/checks').glob('*'):
 if p.is_file():shutil.copy2(p,out/'checks'/p.name)
for name in ('ready_batch4_candidate1.json','collect_ready_drafts.py','promote_batch4.py'):
 shutil.copy2(root/'work'/name,out/name)
p=root/'ASGinzburg.lean';text=p.read_text();matches=list(re.finditer(r'^import .+$',text,re.M));i=matches[-1].end();text=text[:i]+'\n'+'\n'.join('import ASGinzburg.'+n for n in ready)+text[i:];p.write_text(text)
inv=audit_sources.inventory(root)
(root/'AxiomAudit.lean').write_text('import ASGinzburg\n\n'+'\n'.join('#print axioms '+e['name'] for e in inv)+'\n')
record={'promoted_at_utc':datetime.now(timezone.utc).isoformat(),'new_modules':len(ready),'new_declarations':audit['declarations'],
 'public_modules':len(audit_sources.project_sources(root))-1,'public_declarations':len(inv),
 'public_theorems':sum(e['kind'] in ('theorem','lemma') for e in inv),'entries':entries,
 'fresh_full_verification':'not yet started; previous full1251 remains historical successful scope',
 'work_import_normalization':'deferred until new public lake build succeeds; active work checks may continue',
 'github_actions_started':False}
(out/'promotion.json').write_text(json.dumps(record,indent=2)+'\n')
subprocess.run(['python3','work/check_preservation_resume.py',str(out/'preservation-before-full.json')],check=True)
subprocess.run(['git','diff','--check'],check=True)
print(json.dumps({k:v for k,v in record.items() if k!='entries'}))
