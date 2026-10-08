# AS–Ginzburg Lean: 継続作業の規約

## 最初に読むもの

`HANDOFF.md`、`STATUS.md`、`GAPS.md`、`verification/results.json`、
`recovery/recovery_results.json`、`RECENT_RUN.md`を読み、最新の`verification/latest.json`が
指す実行の`run.json`と終了コードを確認する。旧成功記録だけで現在の成功を宣言しない。

## 固定環境と検証

- Lean: `leanprover/lean4:v4.24.0`。
- mathlib: `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`。
- `lake-manifest.json`の全依存コミットを保つ。通常の再現に`lake update`を使わない。
- Python 3、Git、bash、elanまたは固定Leanの配布物を使う。
- 初回は`bash scripts/check.sh --prepare-cache`。依存キャッシュがあれば`bash scripts/check.sh`。
- 固定LeanがPATH外なら`AS_GINZBURG_LEAN_ROOT=/path/to/lean-4.24.0-linux bash scripts/check.sh --prepare-cache`。
- スクリプトは`bash`からも実行でき、`check.sh`と`with_lean.sh`の実行権限をGitに記録する。
- 回帰テストだけなら`python3 -m unittest discover -s tests -v`。
- 毎回新しい`verification/runs/<run-id>/`を作り、実行環境、宣言一覧、`lake build`、
  全明示的宣言の`#print axioms`、終了コード、UTC開始・終了時刻、単調時計の経過秒を保存する。
- 許容公理は`propext`、`Classical.choice`、`Quot.sound`のみ。
  `sorry`、`admit`、独自`axiom`、`sorryAx`、`Lean.ofReduceBool`、`Lean.trustCompiler`は認めない。
- 宣言名・監査コマンド・監査ログの重複、監査漏れ、未対応の宣言構文は失敗とする。
  件数161は初期成果の記録であり、将来の宣言数を固定しない。

## 数学的範囲

定理3.2と系5.2は**未証明で、Leanの形式的な定理文も未実装**。
命題1.4は区間同型を仮定した貼り合わせのみ、命題5.1も未証明。
既存の84補助定理やビルド成功を主定理の完成と扱わない。

2026-10-08のユーザーの明示的な指示により、既存`ZAlgebra.RightModule`の
Abelian圏構造とmathlibのホモロジー代数への接続を実装する数学的形式化を再開した。
この目標を超える数学的形式化の再開・拡張には、ユーザーの別の明示的な指示が必要。
再開の指示を受けても、原論文の仮定を弱めたり、結論と同等の仮定を追加したりしない。
周期性や`WindowSystem`をAS正則性の条件に追加しない。周期性はAS条件から導くべき証明義務。
外部結果を独自公理に置き換えて完成と宣言しない。

## 保存とタスク終了時

旧版、入力PDF、`recovery/`、`checkpoints/`を削除・改変しない。
新しいログは既存の実行ディレクトリへ上書きしない。
`FILES.md`と`recovery/original_file_inventory.json`は回収時の歴史的な一覧であり、現行ツリーの一覧ではない。

タスク終了時は`RECENT_RUN.md`とタスク別の`runs/<task-id>.md`に、目的、差分、
実測開始時刻・終了時刻・経過時間、各検査の終了コード、成功した検査、残ったエラー、
コミット・PR・リモート保存状況を記録する。検証所要時間とタスク全体の所要時間を分ける。
測定していない過去の稼働時間は「不明」とし、推測を実測値として書かない。
`README.md`、`HANDOFF.md`、`STATUS.md`、`GAPS.md`を結果と整合させる。
作業用ブランチへコミットし、可能ならpushとPR作成まで行う。mainへマージしない。
リモートへ保存できない場合は、理由とGit bundle・差分・最新ログを回収できる形で渡す。
