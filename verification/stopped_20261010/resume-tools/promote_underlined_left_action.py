from pathlib import Path
import json,hashlib,shutil,subprocess,datetime,sys,time
root=Path.cwd();sys.path.insert(0,str(root/'scripts'));import audit_sources
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
labels=['current-cut-underlined-left-axioms-1','current-cut-simple-dimension-axioms-1']
audits=[json.loads((Path('work/checks')/(label+'.json')).read_text()) for label in labels]
hashes={}
for a in audits:
 assert a['exit_code']==0 and a['strict_coverage']
 assert set(a['axioms'])<={'propext','Classical.choice','Quot.sound'}
 assert not set(hashes).intersection(a['source_sha256'])
 hashes.update(a['source_sha256'])
paths=[Path(p) for p in sorted(hashes)];assert len(paths)==27 and sum(a['declarations'] for a in audits)==80
records=[]
for p in Path('work/checks').glob('*.json'):
 d=json.loads(p.read_text())
 if d.get('source') in hashes:records.append((p,d))
for p in paths:
 h=hashes[str(p)];assert hashlib.sha256(p.read_bytes()).hexdigest()==h
 assert not (Path('ASGinzburg')/p.name).exists()
 assert any(d['source']==str(p) and d['source_sha256']==h and d['exit_code']==0 for _,d in records)
r=json.loads(Path('verification/results.json').read_text());assert r['module_count']==896 and r['verification_success']
for name,h in r['lean_source_sha256'].items():assert hashlib.sha256(Path(name).read_bytes()).hexdigest()==h,name
dest=Path('verification/cut_underlined_left_action_20261010/current-27');assert not dest.exists();dest.mkdir(parents=True)
for p in paths:shutil.copyfile(p,dest/(p.name+'.draft'))
for p,d in records:
 for f in [p,Path(d['log']),Path(d['source_snapshot'])]:shutil.copyfile(f,dest/f.name)
for label in labels:
 for p in [Path('work')/(label+'.lean'),Path('work/checks')/(label+'.json'),Path('work/checks')/(label+'.log')]:shutil.copyfile(p,dest/p.name)
shutil.copyfile('work/reyes_rogalski_research_20261009.json',dest/'reyes_rogalski_research.json')
prior=json.loads(Path('verification/cut_regular_grading_20261009/full-896/preservation-after-full-896.json').read_text());prior['checked_at_utc']=now
for group in ['initial_mathematical_modules','baseline_60_and_protected_577']:
 for name,d in prior[group].items():
  actual=hashlib.sha256(Path(name).read_bytes()).hexdigest();assert actual==d['expected_sha256'],name
  d['actual_sha256']=actual;d['matches']=True
assert hashlib.sha256(Path('docs/source.pdf').read_bytes()).hexdigest()==prior['source_pdf_sha256']
(dest/'preservation-923.json').write_text(json.dumps(prior,indent=2)+'\n')
mapping={}
for p in paths:
 target=Path('ASGinzburg')/p.name;target.write_text(p.read_text().replace('import work.ASGinzburgDraft.','import ASGinzburg.'))
 mapping[str(target)]={'draft_sha256':hashes[str(p)],'public_sha256':hashlib.sha256(target.read_bytes()).hexdigest()}
p=Path('ASGinzburg.lean');s=p.read_text();idx=s.index('\n/-!');s=s[:idx]+'\n'+''.join('import ASGinzburg.'+p.stem+'\n' for p in paths)+s[idx:];p.write_text(s)
subprocess.run([sys.executable,'scripts/audit_sources.py'],stdout=subprocess.DEVNULL,check=True)
entries=audit_sources.inventory();count=len(list(Path('ASGinzburg').glob('*.lean')));theorems=sum(e['kind']=='theorem' for e in entries)
assert count==923 and len(entries)==4821
meta={'promoted_at_utc':now,'new_mathematical_modules':27,'new_declarations':80,'public_mathematical_modules':count,'public_declarations':len(entries),'public_theorems':theorems,'source_mapping':mapping,'draft_audits':labels,'previous_full_success':r['run_id'],'new_full_verification':'pending','main_theorem_proved':False}
(dest/'promotion-923.json').write_text(json.dumps(meta,indent=2)+'\n')
session=json.loads(Path('work/session_start.json').read_text());elapsed=time.monotonic()-session['started_monotonic']
para=f'''2026-10-10 {now}: 実際の左乗法とExt後合成の単位元/積/両側k線形性から、全内部次数Extへの真のR→End_k表現と通常左R加群を構成。元ASのみからそのkスカラー整合性・通常R有限生成性・頂点冪等元作用、次数0の対角核の具体的冪零性からの指標同定、真の左頂点単純加群とExt³のR線形同型・単純性を証明。実際の直和挿入の像による内部次数分解と左加群の内部shiftを用い、原論文(2.2)の真の次数付き左加群同型underlined Ext³(s_i,R)≃左s_i(1)まで完成。各graded頂点単純の射影次元≤3とτ頂点の射影次元=3も証明。27数学モジュール80宣言の2分割草稿公理監査は実終了0、全80宣言厳密照合・許容3公理のみ・現行SHA一致。公開923数学モジュール/4821宣言/{theorems} theoremの新規全体検証を開始する。直前896構成run20261009T233101Z-7cbcabeeは全体成功・maindfcb6b8保存済みで、この923構成の全体成功とは扱わない。GitHub Actions手動のみ、通常保存[skip ci]、maindfcb6b8のActions実行件数0確認済み。大域次元の上界/Reyes twisted CY/Hanihara/Keller、候補GinzburgRegular・全Jacobian回収・選択独立性/同型類対応・系5.2は未証明。Reyes–Rogalski arXiv:1807.10249v2の命題3.18/定理3.10を一次資料で確認し、次はk^verticesの分離性・真のenveloping環とbalanced tensor/Tor比較を形式化する。定理3.2/系5.2は未証明・正式Lean定理文未実装。引用結果や必要な結論を独自公理/追加仮定にはしていない。\n\n'''
for name in ['README.md','HANDOFF.md','STATUS.md','GAPS.md']:
 p=Path(name);p.write_text(para+p.read_text())
for name in ['RECENT_RUN.md','runs/formalization-continuation-20261009.md']:
 with Path(name).open('a') as f:f.write('\n\n### 全内部次数Extの真の左次数付き双対性を統合\n\n'+para+f'セッション単調時計実測{elapsed:.9f}秒。公開ソースを固定し新規全体検査中もworkで数学を継続する。全失敗/成功ソース・ログ・実終了コード・時刻はcurrent-27へ無変更保存した。保存・チェックポイントだけで終了しない。\n')
print({k:v for k,v in meta.items() if k!='source_mapping'})
