from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,sys
root=Path.cwd();dest=Path(sys.argv[1]);assert not dest.exists()
reference=root/'verification/resume_20261010/batch1/preservation-before-full958.json'
d=json.loads(reference.read_text());result={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'reference':str(reference.relative_to(root)),'comparison_head':d['comparison_head']}
okay=True
for group in ('initial_mathematical_modules','baseline_60_and_protected_577'):
 entries={}
 for name,e in d[group].items():
  actual=hashlib.sha256((root/name).read_bytes()).hexdigest();match=actual==e['expected_sha256'];okay &=match
  entries[name]={'expected_sha256':e['expected_sha256'],'actual_sha256':actual,'matches':match}
 result[group]=entries
h=hashlib.sha256((root/'docs/source.pdf').read_bytes()).hexdigest();result['source_pdf_sha256']=h
result['source_pdf_matches']=h==d['source_pdf_sha256'];okay &=result['source_pdf_matches']
result['exit_code']=0 if okay else 1;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:len(v) if isinstance(v,dict) else v for k,v in result.items()}));sys.exit(result['exit_code'])
