# 再開用引継ぎ

## 最初に読むもの

1. `STATUS.md`：完成・条件付き・未実装の区別。
2. `GAPS.md`：主定理を完成させるための証明義務。
3. `verification/results.json`：今回成功したチェックポイントのハッシュ。

**定理3.2と系5.2は未完成で、Leanの形式的な文もまだ存在しません。**
84補助定理のビルド成功を、主定理の完成と混同しないで下さい。

## 入力の同一性

入力論文は`docs/source.pdf`です。原本のSHA-256は

```text
dd17baddbe17a40cc2117285b65623f58772a5f65ba883146da3ea74290e8a8e
```

13ページ。型Qの一般対応が定理3.2、(3,3,3)型の系が系5.2です。
`docs/source_extracted.txt`は検索用抽出テキストで、数式の確認はPDFを優先します。

## 検証済みの環境

- Lean：`leanprover/lean4:v4.24.0`。
- mathlib：`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`。
- 全14モジュール、84補助定理、161宣言。
- 最後の確実なチェック：`verification/build.log`の全ターゲット成功と、
  `verification/axioms.log`の全宣言監査。
- buildに含まれるプロジェクト内ファイルは全てコンパイルします。
- 独自公理や未証明placeholderはありません。

## 再開する場所

最優先は、`Representables.lean`の`RightModule`をAbelian圏にし、
射影加群・単純加群・最小分解・実際のExtを接続することです。
その後は`GAPS.md`の1、2、3、4、5の順で進めます。
既存補題の仮定を主定理の定義に追加して穴を埋めないで下さい。

## ローカルな再現手順

```bash
lake exe cache get
./scripts/check.sh
```

`check.sh`は宣言一覧を更新し、全ターゲットをビルドし、kernelの公理依存を再記録します。
監査で許すのは`propext`、`Classical.choice`、`Quot.sound`だけです。

今回の実行環境で単体Lean配布を使うための補助設定は次の通りです。

```bash
export AS_GINZBURG_LEAN_ROOT=/absolute/path/to/lean-4.24.0-linux
export AS_GINZBURG_PROC_SELF_FIX=1
./scripts/check.sh
```

`PROC_SELF_FIX`は一部のコンテナの`/proc/<pid>/exe`の参照を補う実行補助です。
通常のMacやLinuxのelan環境では設定せずに使って下さい。
Lean kernelや証明内容を変更するコードではありません。

## ソースファイルの構成

全ファイル一覧と宣言のソース位置は`verification/declarations.json`にあります。
`ASGinzburg.lean`は全モジュールをimportし、`AxiomAudit.lean`は全宣言を監査します。
配布zipにはLeanの実行バイナリやmathlibのキャッシュを含めていません。
固定したバージョンから再取得して検証できます。

## 作業上の注意

- 周期性をAS正則性の仮定に加えない。
- 公理として引用した一般定理を完成した形式化として報告しない。
- 数値的なExt次元表の補題と、実際のExtの計算を区別する。
- cut恒等式と、minimal relation・Jacobian・dg acyclicityを区別する。
- `Classical.choice`などの標準的な論理公理と、未証明の数学を置く独自公理を区別する。
- 新しい数学的障害を見つけたら、実装上の不足と区別して具体的に記録する。
