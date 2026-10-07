# Codexクラウドへの引継ぎ

2026年10月8日（JST）。今回の範囲はビルド再現、公理監査、CI、記録のみです。
新しい数学的形式化・証明変更・公理追加は行っていません。

## 現在の場所と固定環境

- リポジトリ：`https://github.com/uedakazushi/as-ginzburg-lean`。
- クラウドの作業場所：`/workspace/as-ginzburg-lean`。
- 作業ブランチ：`codex/reproduce-audit-ci-20261008`。mainへマージしません。
- Lean：`leanprover/lean4:v4.24.0`。
- mathlib：`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`。lakefileとmanifestで固定。
- 元の場所・旧Git履歴欠落などの回収時点の事実は`recovery/`と`checkpoints/20261007/recovered_docs/`に保存。
  現在のリポジトリには回収後のGit履歴があります。

## 実行結果

最新検証 `20261007T234426Z-5fdb879f`：終了0、12.950793秒。
UTC 2026-10-07T23:44:26.191634+00:00 → 2026-10-07T23:44:39.142436+00:00。
初回の成功検証（キャッシュ準備を含む）は61.159680秒、全段階終了0。

全14数学モジュール、ルートimport、生成監査ターゲットの`lake build`が成功。
全172明示的宣言の`#print axioms`が成功しました。初期161宣言は161異なる名前として列挙し、
既存の名前付きinstance 11件も追加で監査しました。全84補助定理の監査漏れはありません。
161は件数の履歴で、将来の追加を拒む条件ではありません。
`sorry`、`admit`、独自`axiom`は0件。依存は`propext`、`Classical.choice`、`Quot.sound`のみで、
`sorryAx`、`Lean.ofReduceBool`、`Lean.trustCompiler`への依存はありません。
既存の未使用変数・simp引数のlint警告は残りますが、コンパイルエラーはありません。

## 同一性と旧版の保存

14数学モジュールと`ASGinzburg.lean`は旧results.jsonのSHA-256にすべて一致し、無変更です。
入力PDFも旧ハッシュに一致します。`recovery/`は無変更。
旧`verification/`の4ファイルは`checkpoints/20261007/verification/`へバイト単位で保存。
旧`AxiomAudit.lean`、改訂前のREADME・引継ぎ・状況・不足・宣言・ファイル一覧も保存しました。
詳細は`checkpoints/20261007/preservation.json`にあります。

## 公理監査の修正

旧スクリプトは`InWindow.mono`を切り詰め、161コマンドで160異なる名前だけを監査していました。
今回、`ASGinzburg.ZAlgebra.InWindow.mono`を完全名で列挙し、ソース一覧・監査コマンド・ログを
それぞれ重複検査して一対一で照合します。現在のソース一覧とも照合し、未対応の宣言構文は失敗します。
Nested commentを除去してソース位置を保持し、ルートimportファイルもplaceholder検査に含めます。
旧監査記録を全161宣言の成功証拠と解釈してはいけません。

`AxiomAudit.lean`の差分は、重複したInWindowコマンドをInWindow.monoへ訂正し、
既存instance 11件への監査コマンドを加えたものです。数学的宣言は追加していません。
旧SHA-256：`06d8eced449f4f0e3a4e67a6eeda093e8aa037b5b4c729881f1e9001aeaa0dde`。
新SHA-256：`105c8fb83f0740d8d3b30b34f018ad4adbc0b3992b0743d96706c945268ed39d`。

## 次の検証とCI

```bash
USE_FRO_CACHE=1 AS_GINZBURG_LEAN_ROOT=/workspace/.cloud-setup/lean-4.24.0-linux \
  bash scripts/check.sh --prepare-cache
```

キャッシュがあれば`--prepare-cache`を省略できます。通常はPATH上の固定elan/Leanでも実行できます。
Gitにシェルの実行権限を記録し、内部呼出しもbash経由にしました。
キャッシュは`.lake/cache/mathlib/`を使います。通常の再現に`lake update`は不要です。
今回、ホームへの書込み失敗、ネットワーク権限不足、Azure取得先のCONNECT 403を観測しました。
書込み先を修正し、許可されたネットワークとmathlib対応のCloudflareキャッシュで解決しました。
途中で停止したソースビルド・全mathlibキャッシュ取得も含め、失敗試行は各runに保存しています。

CIはpush/pull_requestで同じ固定版と検証コマンドを使い、終了コードを反映します。
今回のrunだけをartifactへ保存し、履歴の成功ログで判定しません。
最終のリモート保存・PR・Actions状況は`RECENT_RUN.md`を確認してください。

## 主結果

定理3.2・系5.2は**未証明、形式的な定理文も未実装**です。
命題1.4は区間同型を仮定した貼り合わせのみ、命題5.1も未証明です。
補助定理の成功を主結果の完成として扱わないでください。
原論文の仮定を弱めず、周期性をAS条件に追加しません。
数学的形式化を再開するには別の明示的な指示が必要です。`AGENTS.md`、`STATUS.md`、`GAPS.md`を参照。
過去の作業全体の稼働時間は不明であり、今回の実測時間と混同しません。
