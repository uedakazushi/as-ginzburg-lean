from pathlib import Path
import hashlib,json,re,sys
root=Path.cwd();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
checks=[];audits=[]
for p in sorted((root/'work/checks').glob('*.json')):
 try:d=json.loads(p.read_text())
 except json.JSONDecodeError:continue
 if d.get('exit_code')==0:
  checks.append((p,d))
  if d.get('strict_coverage') and isinstance(d.get('source_sha256'),dict):audits.append((p,d))
ready={};excluded={}
for p in sorted((root/'work/ASGinzburgDraft').glob('*.lean')):
 if (root/'ASGinzburg'/p.name).exists():continue
 name=p.stem;rel=str(p.relative_to(root));h=sha(p)
 individual=[str(q.relative_to(root)) for q,d in checks if d.get('source')==rel and d.get('source_sha256')==h
  and (root/d.get('log','')).is_file() and sha(root/d['log'])==d.get('log_sha256') and not (root/d['log']).read_text().strip()]
 audited=[str(q.relative_to(root)) for q,d in audits if d['source_sha256'].get(rel)==h
  and (root/d.get('log','')).is_file() and sha(root/d['log'])==d.get('log_sha256')]
 deps=re.findall(r'^import work\.ASGinzburgDraft\.([A-Za-z0-9_]+)$',p.read_text(),re.M)
 if individual and audited:ready[name]={'source':rel,'sha256':h,'individual_checks':individual,'strict_audits':audited,'draft_imports':deps}
 else:excluded[name]={'individual_success':bool(individual),'strict_audit_success':bool(audited),'draft_imports':deps}
changed=True
while changed:
 changed=False
 for name,e in list(ready.items()):
  missing=[n for n in e['draft_imports'] if n not in ready and not (root/'ASGinzburg'/(n+'.lean')).exists()]
  if missing:
   excluded[name]={'missing_checked_closure':missing};del ready[name];changed=True
out=Path(sys.argv[1]);assert not out.exists();out.write_text(json.dumps({'ready':ready,'excluded':excluded},indent=2)+'\n')
print(json.dumps({'ready_modules':len(ready),'excluded':excluded},ensure_ascii=False))
