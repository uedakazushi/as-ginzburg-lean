from pathlib import Path
import datetime
import hashlib
import json
import shutil
import subprocess
import time

root = Path.cwd()
started = datetime.datetime.now(datetime.timezone.utc).isoformat()
tick = time.monotonic()
run_id = '20261010T000102Z-e3e135f8'
result = json.loads(Path('verification/results.json').read_text())
run = json.loads((Path('verification/runs') / run_id / 'run.json').read_text())
wrapper = json.loads(Path('work/full923_logged_20261010T000101Z.json').read_text())
assert result['run_id'] == run['run_id'] == run_id
assert run['status'] == 'success' and run['exit_code'] == result['exit_code'] == wrapper['exit_code'] == 0
assert result['verification_success'] and result['module_count'] == 923
assert result['declaration_count'] == result['unique_declaration_count'] == 4821
assert result['theorem_count'] == 2661
assert len(run['steps']) == 6 and all(s['exit_code'] == 0 for s in run['steps'])
assert set(result['kernel_axiom_dependencies']) == {'propext', 'Classical.choice', 'Quot.sound'}
assert not any(result[k] for k in ['missing_theorems', 'unchecked_proof_dependencies', 'source_placeholders', 'main_theorem_proved', 'main_theorem_formal_statement_implemented'])
assert len(result['lean_source_sha256']) == 925
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
for name, expected in result['lean_source_sha256'].items():
    assert sha(name) == expected, name

dest = Path('verification/stopped_20261010')
assert not dest.exists()
dest.mkdir()
full = Path('verification/cut_underlined_left_action_20261010/full-923')
assert not full.exists()
full.mkdir()
preservation = json.loads(Path('verification/cut_underlined_left_action_20261010/current-27/preservation-923.json').read_text())
for group in ['initial_mathematical_modules', 'baseline_60_and_protected_577']:
    for name, entry in preservation[group].items():
        actual = sha(name)
        assert actual == entry['expected_sha256'], name
        entry['actual_sha256'] = actual
        entry['matches'] = True
assert sha('docs/source.pdf') == preservation['source_pdf_sha256'] == result['source_paper_sha256']
for name in ['lean-toolchain', 'lake-manifest.json']:
    assert Path(name).read_bytes() == subprocess.check_output(['git', 'show', 'dfcb6b8:' + name]), name
preservation['checked_at_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
preservation['exit_code'] = 0
(full / 'preservation-after-full-923.json').write_text(json.dumps(preservation, indent=2) + '\n')
for name in ['full923_logged_20261010T000101Z.json', 'full923_logged_20261010T000101Z.log']:
    shutil.copyfile(Path('work') / name, full / name)
shutil.copyfile('work/checkpoint_separability_20261010T0016.json', full / 'checkpoint-before-success.json')
(full / 'full-success-923.json').write_text(json.dumps({
    'checked_at_utc': preservation['checked_at_utc'], 'run_id': run_id,
    'exit_code': 0, 'module_count': 923, 'declaration_count': 4821,
    'theorem_count': 2661, 'lean_source_count': 925,
    'public_source_sha_match': True, 'preservation_exit_code': 0,
    'dependencies_unchanged': True, 'elapsed_seconds': run['elapsed_seconds'],
    'main_theorem_proved': False, 'later_drafts_outside_full_run': True,
}, indent=2) + '\n')

drafts = sorted(p for p in Path('work/ASGinzburgDraft').glob('*.lean') if not (Path('ASGinzburg') / p.name).exists())
assert len(drafts) == 15
draft_dir = dest / 'drafts'
checks_dir = dest / 'checks'
helper_dir = dest / 'resume-tools'
for p in [draft_dir, checks_dir, helper_dir]:
    p.mkdir()
records = []
for p in Path('work/checks').glob('*.json'):
    try:
        value = json.loads(p.read_text())
    except json.JSONDecodeError:
        continue
    records.append((p, value))
inventory = []
copied = set()
def copy_check(path):
    path = Path(path)
    if not path.exists():
        raise FileNotFoundError(path)
    target = checks_dir / path.name
    if path.name in copied:
        assert target.read_bytes() == path.read_bytes()
    else:
        shutil.copyfile(path, target)
        copied.add(path.name)
for p in drafts:
    h = sha(p)
    archived = draft_dir / (p.name + '.draft')
    shutil.copyfile(p, archived)
    matching = [(j, d) for j, d in records if d.get('source') == str(p)]
    matching.sort(key=lambda t: t[1].get('started_at_utc', ''))
    current = [(j, d) for j, d in matching if d.get('source_sha256') == h]
    latest = current[-1] if current else None
    status = 'not_checked' if latest is None else ('individual_lean_success_only' if latest[1]['exit_code'] == 0 else 'individual_lean_failed')
    for j, d in matching:
        for f in [j, Path(d['log']), Path(d['source_snapshot'])]:
            copy_check(f)
    inventory.append({
        'working_source': str(p), 'archived_source': str(archived), 'sha256': h,
        'status': status, 'individual_check_records': [str(checks_dir / j.name) for j, d in matching],
        'latest_current_check': None if latest is None else str(checks_dir / latest[0].name),
        'axiom_audit_status': 'not_run', 'full_verification_scope': False,
    })
for label in ['separability-pinned-mathlib-dependencies-1', 'ordinary-projective-pinned-mathlib-dependency-1']:
    for suffix in ['.json', '.log']:
        copy_check(Path('work/checks') / (label + suffix))
for name in ['check_module.py', 'audit_current_drafts.py', 'run_full923_logged.py', 'promote_underlined_left_action.py']:
    shutil.copyfile(Path('work') / name, helper_dir / name)
for name in ['session_start.json', 'checkpoint_separability_20261010T0016.json', 'full923_active.json', 'reyes_rogalski_research_20261009.json']:
    shutil.copyfile(Path('work') / name, dest / name)
shutil.copyfile(__file__, helper_dir / Path(__file__).name)
assert sum(x['status'] == 'individual_lean_success_only' for x in inventory) == 12
assert sum(x['status'] == 'individual_lean_failed' for x in inventory) == 2
assert sum(x['status'] == 'not_checked' for x in inventory) == 1

processes = []
for p in Path('/proc').iterdir():
    if not p.name.isdigit():
        continue
    try:
        comm = (p / 'comm').read_text().strip()
        args = (p / 'cmdline').read_bytes().split(b'\0')
    except (FileNotFoundError, PermissionError, ProcessLookupError):
        continue
    if comm == 'lean' or any(a.startswith((b'scripts/check.sh', b'scripts/run_axiom_audit.py', b'work/run_full', b'work/check_module.py', b'work/audit_current_drafts.py')) for a in args):
        processes.append({'pid': int(p.name), 'command': comm})
assert not processes, processes
session = json.loads(Path('work/session_start.json').read_text())
ended = datetime.datetime.now(datetime.timezone.utc).isoformat()
meta = {
    'status': 'stopped_by_user', 'reason': '作業を中止して保存して下さい。',
    'recording_started_at_utc': started, 'recording_ended_at_utc': ended,
    'recording_elapsed_seconds': time.monotonic() - tick,
    'session_elapsed_seconds_including_idle': time.monotonic() - session['started_monotonic'],
    'last_full_success': run_id, 'last_full_exit_code': 0,
    'full_public_module_count': 923, 'full_declaration_count': 4821,
    'full_public_source_sha_match': True, 'preservation_exit_code': 0,
    'active_formalization_processes': processes,
    'new_formalization_or_builds_started_after_stop_request': False,
    'github_actions_started_for_this_save': 0,
    'pre_save_main_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
    'save_target': 'https://github.com/uedakazushi/as-ginzburg-lean main',
    'save_status_at_recording': 'prepared_for_regular_fast_forward_commit_and_push',
    'main_theorem_proved': False, 'main_theorem_formal_statement_implemented': False,
    'drafts': inventory,
    'next_proof_obligations_on_explicit_resume': [
        'Correct the Functor.Linear.map_smul binder order in BalancedTensorRightFunctor, then check it.',
        'Prove projectivity of actual finite coproducts and retracts in PeriodCutOrdinaryFiniteProjectives.',
        'Check PeriodCutCornerFieldTotalNaturality; establish exactness of forgetting the grading and transport the finite AS resolution.',
        'Audit individually checked drafts before promotion; formalize genuine tensor-Hom adjunction and derived Tor comparison.',
        'Continue global dimension, Reyes–Rogalski/Hanihara/Keller, full Jacobian recovery, choice independence and Corollary 5.2 without extra axioms.',
    ],
}
(dest / 'stop-state.json').write_text(json.dumps(meta, ensure_ascii=False, indent=2) + '\n')
summary = f'''ユーザーの「作業を中止して保存して下さい。」により形式化を停止した。検証プロセスは稼働しておらず、新しい証明修正・ビルド・公理監査は開始していない。再開はユーザーの指示を待つ。

最新の公開923数学モジュール・4821異なる宣言・2661 theoremは、run `{run_id}` において全6段階実終了0。925公開LeanソースのSHAが検査時のソースと完全一致し、初期14・開始時60と577保護ファイル・入力PDF・固定依存の無変更確認も終了0。全宣言の公理依存は `propext`、`Classical.choice`、`Quot.sound` のみ。検証の実測UTC開始 `{run['started_at_utc']}`、終了 `{run['ended_at_utc']}`、単調時計経過 {run['elapsed_seconds']:.9f} 秒。wrapper実終了0・経過 {wrapper['elapsed_seconds']:.9f} 秒。これらは停止前に開始して完了していた検証の記録である。

原論文(2.2)の真の左R加群作用と内部次数に適合する underlined Ext³(s_i,R) ≃ 左s_i(1)、各graded頂点単純の射影次元≤3とτ頂点での射影次元=3まで、この全体検証の範囲で確認した。

後続15草稿は `verification/stopped_20261010/drafts/` に元ソースと同じSHAで保存した。12件は個別Lean終了0のみ、公理監査未実施。2件は現行ソースの個別Lean終了1、1件は未検査。これらを公開923モジュールの全体成功の対象とは扱わない。全ての成功・失敗ログ、実測時刻・終了コード・ソーススナップショットを `verification/stopped_20261010/checks/` に保持した。

未完了箇所：BalancedTensorRightFunctor の Linear.map_smul の束縛順、有限直和・retract の通常射影性、CornerFieldTotalNaturality の未検査。次は次数を忘れる関手の完全性と通常の有限AS射影分解、tensor-Hom/derived Tor比較、大域次元、Reyes–Rogalski/Hanihara/Keller、全Jacobian回収・選択独立性・系5.2。定理3.2と系5.2は未証明・正式Lean定理文未実装であり、必要な結論を公理や追加仮定にしていない。

mainの直前保存は `dfcb6b85db87d4b5095454c24108c34973a53557`。今回の差分・全体検証証拠・未完成草稿・引継ぎを `[skip ci]` 付き通常コミットで直接mainへ保存する。workflowは workflow_dispatch のみで、GitHub Actionsを起動しない。保存コミットはGit履歴で確認できる。詳細な停止状態と次の手順は `verification/stopped_20261010/stop-state.json` に記録した。
'''
for name in ['README.md', 'HANDOFF.md', 'STATUS.md', 'GAPS.md']:
    p = Path(name)
    p.write_text('## ユーザー指示による停止・保存（2026-10-10）\n\n' + summary + '\n以下は当時の履歴として保持する。\n\n' + p.read_text())
for name in ['RECENT_RUN.md', 'runs/formalization-continuation-20261009.md']:
    with Path(name).open('a') as f:
        f.write('\n\n### ユーザー指示による停止・保存（2026-10-10）\n\n' + summary + f'\n停止記録作成：UTC {started} → {ended}、単調時計実測 {meta["recording_elapsed_seconds"]:.9f} 秒。セッション起点からの経過は {meta["session_elapsed_seconds_including_idle"]:.9f} 秒（待機・中断を含み、証明作業時間とは区別する）。今回の停止理由はユーザー指示であり、実行制限ではない。\n')
(dest / 'README.md').write_text(summary + '\n再開時は drafts/*.lean.draft を stop-state.json の working_source へ復元し、元SHAを照合する。公開ソースは全体検証済みであり、未完成草稿のimportを公開入口へ追加しない。resume-tools/ に個別検査・草稿監査の補助スクリプトを保存した。\n')
snapshot_hashes = {str(p): sha(p) for base in [dest, full] for p in sorted(base.rglob('*')) if p.is_file()}
(dest / 'archive-sha256.json').write_text(json.dumps(snapshot_hashes, indent=2) + '\n')
print(json.dumps({k: v for k, v in meta.items() if k != 'drafts'}, ensure_ascii=False, indent=2))
print('Archived draft count:', len(inventory), 'Archived check files:', len(copied))
