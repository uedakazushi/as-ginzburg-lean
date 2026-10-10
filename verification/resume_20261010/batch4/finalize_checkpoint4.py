from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time,shutil
root=Path.cwd();runpath=root/'verification/runs/20261010T053852Z-1116dc15/run.json'
run=json.loads(runpath.read_text())
assert run['status']=='success' and len(run['steps'])==6
assert all(s['exit_code']==0 for s in run['steps'])
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert all(sha(root/p)==h for p,h in run['lean_source_sha256'].items())
res=json.loads((runpath.parent/'results.json').read_text())
assert res['module_count']==1372 and res['declaration_count']==6909 and res['theorem_count']==3877
wrapper=root/'work/full_batch4_logged_20261010T053852Z.json';w=json.loads(wrapper.read_text())
assert w['exit_code']==0
out=root/'verification/resume_20261010/batch4';dest=out/'full1372-completion.json'
assert not dest.exists()
subprocess.run(['python3','work/check_preservation_resume.py',str(out/'preservation-after-full1372.json')],check=True)
for name in ('lean-toolchain','lake-manifest.json','lakefile.toml'):
    p=root/name
    if p.exists():assert p.read_bytes()==subprocess.check_output(['git','show','d847693aee04819ccc7264bae839ce899d436709:'+name])
for p in (wrapper,root/'work/full_batch4_logged_20261010T053852Z.log',root/'work/run_full_batch4_logged.py',
          root/'work/finalize_checkpoint4.py',root/'work/check_preservation_resume.py'):
    shutil.copy2(p,out/p.name)
now=datetime.now(timezone.utc);start=json.loads((root/'work/resume_start.json').read_text())
completion={'checked_at_utc':now.isoformat(),'run_id':run['run_id'],'status':run['status'],
 'modules':1372,'declarations':6909,'theorems':3877,'new_modules':121,'new_declarations':689,
 'run_started_at_utc':run['started_at_utc'],'run_ended_at_utc':run['ended_at_utc'],
 'run_elapsed_seconds':run['elapsed_seconds'],'steps':[(s['stage'],s['exit_code']) for s in run['steps']],
 'wrapper':w,'current_public_sources_match_run':True,'pinned_dependency_files_unchanged':True,
 'github_actions_started':False,'main_save_status':'verified checkpoint ready for direct normal main push',
 'session_started_at_utc':start['started_at_utc'],'session_checkpoint_at_utc':now.isoformat(),
 'session_elapsed_seconds':time.monotonic()-start['monotonic'],'continuation_active':True,
 'main_theorems_complete':False}
dest.write_text(json.dumps(completion,indent=2)+'\n')
block=f'''検証済み公開保存点（UTC {now.isoformat()}、数学的作業は継続中）：121モジュール / 689宣言を追加した1372数学モジュール / 6909宣言 / 3877 theoremの新規全体run `{run['run_id']}` は全6段階実終了0・success。UTC `{run['started_at_utc']}` → `{run['ended_at_utc']}`、実測{run['elapsed_seconds']:.9f}秒。wrapper実終了0・実測{w['elapsed_seconds']:.9f}秒。全6909異なる宣言の厳密公理照合と現行公開SHA一致、許容公理 `propext` / `Classical.choice` / `Quot.sound` のみ。固定依存・初期14 / 開始時60+577保護記録 / 入力PDFの無変更照合も0。

公開追加：実際のポテンシャルのHH0巡回商への単射、道代数自己同型の作用と軌道、任意の非線形置換に対する巡回微分連鎖律、真のJacobianイデアルの移送とunrolled Jacobian同型への下降を証明した。正則ポテンシャルの自己同型軌道から頂点固定AS代数同型類への写像は下降済み。三角quiverの実際の自己同型群≃GL(3)³とテンソル軌道の一致、定理3.2・系5.2の元仮定を保つ対応命題、系5.2の三角場合への還元、実際の二次AS分解/成分次元条件から周期3とHilbert値、一般quiverのEuler式による成分次元一意性を追加した。有限射影環双対・bidual・derived Extの有限cochain模型、Ae双対各項の実際の内部次数と下界/微分次数保存、右Aeから右Rへの射影性保存、実際の次数付き四項複体の半単純テンソル完全性検出も公開した。定理3.2・系5.2の証明、対応の単射性と全AS代数回復、twisted CYの集中と可逆性、Reyes–Rogalski / Hanihara / Kellerの核は未完成。以後の三角基底比較・三角軌道回復・普通Ext集中・次数付き被覆の草稿は1372全体検査の対象外として保存する。GitHub Actionsを使わず検証済み差分を直接mainへ通常pushし、その後も必要な証明義務へ継続する。

以下の検査進行中記録は当時の履歴として保持する。

'''
for name in ('README.md','HANDOFF.md','STATUS.md','GAPS.md','RECENT_RUN.md','runs/formalization-resume-20261010.md'):
    p=root/name;s=p.read_text()
    old='最新の公開全体成功は1251数学モジュール / 6220宣言のrun `20261010T043623Z-ba37043f`。'
    assert old in s
    s=s.replace(old,'最新の公開全体成功は1372数学モジュール / 6909宣言のrun `20261010T053852Z-1116dc15`。',1)
    p.write_text(block+s)
subprocess.run(['python3','work/save_resume_checkpoint4.py'],check=True)
subprocess.run(['git','diff','--check'],check=True)
print(json.dumps({k:v for k,v in completion.items() if k!='wrapper'}))
