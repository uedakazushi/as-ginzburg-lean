from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time,shutil
root=Path.cwd();runpath=root/'verification/runs/20261010T020006Z-65de0cea/run.json';run=json.loads(runpath.read_text())
assert run['status']=='success',run['status'];assert len(run['steps'])==6 and all(s['exit_code']==0 for s in run['steps'])
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert all(sha(root/p)==h for p,h in run['lean_source_sha256'].items())
res=json.loads((runpath.parent/'results.json').read_text());assert res['module_count']==958 and res['declaration_count']==4977 and res['theorem_count']==2728
wrapper=root/'work/full958_logged_20261010T020006Z.json';w=json.loads(wrapper.read_text());assert w['exit_code']==0
out=root/'verification/resume_20261010/batch1';dest=out/'full958-completion.json';assert not dest.exists()
subprocess.run(['python3','work/check_preservation_resume.py',str(out/'preservation-after-full958.json')],check=True)
for name in ('lean-toolchain','lake-manifest.json','lakefile.toml'):
 p=root/name
 if p.exists():assert p.read_bytes()==subprocess.check_output(['git','show','d847693aee04819ccc7264bae839ce899d436709:'+name])
for p in (wrapper,root/'work/full958_logged_20261010T020006Z.log',root/'work/finalize_checkpoint1.py',root/'work/check_preservation_resume.py'):
 shutil.copy2(p,out/p.name)
now=datetime.now(timezone.utc);start=json.loads((root/'work/resume_start.json').read_text())
completion={'checked_at_utc':now.isoformat(),'run_id':run['run_id'],'status':run['status'],'modules':958,'declarations':4977,'theorems':2728,
 'run_started_at_utc':run['started_at_utc'],'run_ended_at_utc':run['ended_at_utc'],'run_elapsed_seconds':run['elapsed_seconds'],
 'steps':[(s['stage'],s['exit_code']) for s in run['steps']],'wrapper':w,'current_public_sources_match_run':True,
 'pinned_dependency_files_unchanged':True,'github_actions_started':False,'main_save_status':'verified checkpoint ready for direct normal main push',
 'session_started_at_utc':start['started_at_utc'],'session_checkpoint_at_utc':now.isoformat(),'session_elapsed_seconds':time.monotonic()-start['monotonic'],
 'continuation_active':True,'main_theorems_complete':False}
dest.write_text(json.dumps(completion,indent=2)+'\n')
block=f'''検証済み公開保存点（UTC {now.isoformat()}、数学的作業は継続中）：35モジュール / 156宣言を公開へ追加した958数学モジュール / 4977宣言 / 2728 theoremの新規全体run `{run['run_id']}` は全6段階実終了0・success。UTC `{run['started_at_utc']}` → `{run['ended_at_utc']}`、実測{run['elapsed_seconds']:.9f}秒。wrapper実終了0・実測{w['elapsed_seconds']:.9f}秒。全4977異なる宣言の厳密公理照合と現行公開SHA一致、許容公理 `propext` / `Classical.choice` / `Quot.sound` のみ。固定依存・初期14 / 開始時60+577保護記録 / 入力PDFの無変更照合も0。\n\n今回の公開追加は非可換balanced tensorの実際の商、tensor-Hom随伴、左右加法的関手、実際の導来Torと真の最小分解による計算、次数0のenveloping比較、scalar-product separabilityと半単純商の実際頂点分解・射影次元上界。後続の通常AS分解・射影次元=3・Nakayama・最小分解存在・包絡環分解などの草稿は、この958公開全体検証の対象外として別保存する。包絡環Rの有限分解存在、大域次元の上界、Reyes–Rogalski / Hanihara / Keller、定理3.2と系5.2は未完成。GitHub Actionsは使用せず、検証済み差分を直接mainへ通常pushし、その後も次の証明義務へ継続する。\n\n'''
for name in ('README.md','HANDOFF.md','STATUS.md','GAPS.md','RECENT_RUN.md','runs/formalization-resume-20261010.md'):
 p=root/name;s=p.read_text();old='最新の公開全体成功は923数学モジュール / 4821宣言のrun `20261010T000102Z-e3e135f8`。'
 assert old in s;s=s.replace(old,'最新の公開全体成功は958数学モジュール / 4977宣言のrun `20261010T020006Z-65de0cea`。',1)
 marker='再開チェックポイント（UTC 2026-10-10T02:42:06';i=s.index(marker);s=s[:i]+block+s[i:];p.write_text(s)
subprocess.run(['python3','work/save_resume_checkpoint.py'],check=True)
subprocess.run(['git','diff','--check'],check=True)
print(json.dumps({k:v for k,v in completion.items() if k!='wrapper'}))
