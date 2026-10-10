from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time,shutil
root=Path.cwd();runpath=root/'verification/runs/20261010T043623Z-ba37043f/run.json'
run=json.loads(runpath.read_text())
assert run['status']=='success' and len(run['steps'])==6
assert all(s['exit_code']==0 for s in run['steps'])
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert all(sha(root/p)==h for p,h in run['lean_source_sha256'].items())
res=json.loads((runpath.parent/'results.json').read_text())
assert res['module_count']==1251 and res['declaration_count']==6220 and res['theorem_count']==3449
wrapper=root/'work/full_batch3_logged_20261010T043623Z.json';w=json.loads(wrapper.read_text())
assert w['exit_code']==0
out=root/'verification/resume_20261010/batch3';dest=out/'full1251-completion.json'
assert not dest.exists()
subprocess.run(['python3','work/check_preservation_resume.py',str(out/'preservation-after-full1251.json')],check=True)
for name in ('lean-toolchain','lake-manifest.json','lakefile.toml'):
    p=root/name
    if p.exists():assert p.read_bytes()==subprocess.check_output(['git','show','d847693aee04819ccc7264bae839ce899d436709:'+name])
for p in (wrapper,root/'work/full_batch3_logged_20261010T043623Z.log',root/'work/run_full_batch3_logged.py',
          root/'work/finalize_checkpoint3.py',root/'work/check_preservation_resume.py'):
    shutil.copy2(p,out/p.name)
now=datetime.now(timezone.utc);start=json.loads((root/'work/resume_start.json').read_text())
completion={'checked_at_utc':now.isoformat(),'run_id':run['run_id'],'status':run['status'],
 'modules':1251,'declarations':6220,'theorems':3449,'new_modules':161,'new_declarations':749,
 'run_started_at_utc':run['started_at_utc'],'run_ended_at_utc':run['ended_at_utc'],
 'run_elapsed_seconds':run['elapsed_seconds'],'steps':[(s['stage'],s['exit_code']) for s in run['steps']],
 'wrapper':w,'current_public_sources_match_run':True,'pinned_dependency_files_unchanged':True,
 'github_actions_started':False,'main_save_status':'verified checkpoint ready for direct normal main push',
 'session_started_at_utc':start['started_at_utc'],'session_checkpoint_at_utc':now.isoformat(),
 'session_elapsed_seconds':time.monotonic()-start['monotonic'],'continuation_active':True,
 'main_theorems_complete':False}
dest.write_text(json.dumps(completion,indent=2)+'\n')
block=f'''検証済み公開保存点（UTC {now.isoformat()}、数学的作業は継続中）：161モジュール / 749宣言を追加した1251数学モジュール / 6220宣言 / 3449 theoremの新規全体run `{run['run_id']}` は全6段階実終了0・success。UTC `{run['started_at_utc']}` → `{run['ended_at_utc']}`、実測{run['elapsed_seconds']:.9f}秒。wrapper実終了0・実測{w['elapsed_seconds']:.9f}秒。全6220異なる宣言の厳密公理照合と現行公開SHA一致、許容公理 `propext` / `Classical.choice` / `Quot.sound` のみ。固定依存・初期14 / 開始時60+577保護記録 / 入力PDFの無変更照合も0。

公開追加：元のAS条件だけから実際の包絡環Ae正則加群の有限四項最小射影分解、Ae射影次元=3、全ての通常右・左加群の射影次元≤3と左右の大域次元=3、実際の有限射影cochain complexによるcut代数のホモロジー的滑らかさを証明した。Aeの実際の次数・augmentation核・半単純商、通常Torとの比較と左右バランス、有限topから有限生成性、元AS条件からのAe最小被覆・分解の存在を含む。AS正則代数の実際の頂点固定同型類、Ginzburg正則ポテンシャルからその同型類への写像、実際の巡回商HH0と道トレースも公開した。Reyes–Rogalski / Hanihara / Kellerの核となるtwisted CY・導来同値、定理3.2と系5.2の証明は未完成。後続の実際のポテンシャル巡回商単射・道代数自己同型軌道・対応命題の定義・有限射影双対モデルは、この1251全体検証対象外として別保存する。GitHub Actionsを使わず検証済み差分を直接mainへ通常pushし、その後も次の証明義務へ継続する。

以下の検査進行中記録は当時の履歴として保持する。

'''
for name in ('README.md','HANDOFF.md','STATUS.md','GAPS.md','RECENT_RUN.md','runs/formalization-resume-20261010.md'):
    p=root/name;s=p.read_text()
    old='最新の公開全体成功は1090数学モジュール / 5471宣言のrun `20261010T030805Z-c1036dae`。'
    assert old in s
    s=s.replace(old,'最新の公開全体成功は1251数学モジュール / 6220宣言のrun `20261010T043623Z-ba37043f`。',1)
    p.write_text(block+s)
subprocess.run(['python3','work/save_resume_checkpoint3.py'],check=True)
subprocess.run(['git','diff','--check'],check=True)
print(json.dumps({k:v for k,v in completion.items() if k!='wrapper'}))
