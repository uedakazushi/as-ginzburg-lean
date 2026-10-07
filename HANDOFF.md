# 回収・引継ぎ記録

今回の指示は成果の回収のみです。新しいLean形式化・証明修正・公理追加は行っていません。
回収日時（UTC）：2026-10-07T21:01:24.323045+00:00

## 場所と保存範囲

- 現在の復元プロジェクト：`/workspace/scratch/0a3c62d44058/recovery/as_ginzburg_lean`。
- 元の作業場所：`/workspace/scratch/0a3c62d44058/as_ginzburg_lean`。現在は存在しません。
- 復元先はGitリポジトリではありません。Git履歴は元の保存zipに含まれず、外部リポジトリの所在を確認する記録もありません。
- 元チェックポイント：`as_ginzburg_lean_20261007_checkpoint.zip`（35ファイル）。今回の回収パッケージにも無変更で同梱。
- `FILES.md`：回収した全ファイルの区分・サイズ・ハッシュ。
- `DECLARATIONS.md`：完成済みの全161宣言の完全名・種別・ソース位置。
- 旧引継ぎ文書3点：`recovery/checkpoint_docs/`。

## 今回の検査と最後の成功

現在の `lake build` は終了コード127、`lake: command not found`。現在のLean／lakeおよび依存キャッシュがないため、コンパイルの再検証はできていません。これはLeanソースのコンパイルエラーではありません。
新しい形式化や依存環境の再構築には着手せず、回収を完了しています。

最後の確実な成功は **2026-10-07 08:37:54.907799 UTC** のチェックポイントです。
`verification/build.log` は `Build completed successfully (3123 jobs).` を記録しています。
Lean 4.24.0、mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`。
全16 Leanソースと論文PDFのSHA-256を旧results.jsonと照合し、すべて一致しました。
旧verification/は上書きしていません。

## 監査記録の訂正

旧監査スクリプトはドットを含む宣言名を途中で切り、`InWindow.mono`を`InWindow`と誤記しています。
旧AxiomAudit.leanは161コマンドですが160個の異なる名前を監査し、`ASGinzburg.ZAlgebra.InWindow.mono`の個別公理監査が抜けています。
記録された160宣言の依存公理は`propext`、`Classical.choice`、`Quot.sound`のみ。
「全161宣言を個別監査済み」という旧文書の主張を訂正します。
この補題は全体ビルドの成功範囲には入っています。今回は監査スクリプト・Leanファイルを修正していません。

## 主結果・未完了事項

定理3.2と系5.2はLeanでの定理文自体が未実装です。命題1.4は区間同型を仮定した貼り合わせ段階だけ、命題5.1も未証明です。
84個は補助定理です。AS条件からの周期性を完成したとは扱えません。
原論文との詳細な対応はSTATUS.md、数学的・Lean上の不足はGAPS.mdを参照してください。
数学的反例を発見したという記録はありません。

## 再現用情報（今回未実行）

Lean 4.24.0と固定された依存関係を別途用意すれば `lake build` を実行できます。
zipから展開したscripts/は実行権限を保持していないため、シェルスクリプトは `bash scripts/with_lean.sh lake build` のように呼び出せます。
`check.sh`は監査一覧と旧verification/を上書きするため、元の記録を保存してから使う必要があります。
また、そのままでは上記のドット付き宣言名の監査不足が再発します。
今回の回収結果は `recovery/recovery_results.json` と `recovery/current_build.log` にあります。
