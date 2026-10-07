# AS–Ginzburg対応のLean形式化：検証済みチェックポイント

**主定理全体は未完成です。定理3.2と系5.2の形式的な文も、まだ実装していません。**

添付論文を読み、具体的な代数・道・巡回微分・テンソル積の定義と補助定理を実装しました。
14モジュール、84補助定理、161宣言についてビルドと公理依存の監査が成功しています。
数学的な証明に使う定義・仮定は各宣言の型に明記してあります。
独自公理、`sorry`、`admit`を使って主定理を完成扱いにすることはしていません。

## 確認済みの代表的な内容

- cut付き有限箙と被覆の頂点、heightの全単射、winding degreeの正値性。
- 道の線形化、双線形な積、局所単位元、結合則。
- 実際の局所有限な正に有向なZ-代数と、そのk線形圏・右表現可能加群。
- 線形Yonedaによる表現可能加群のHomの同定と、逆方向のHomの消滅。
- 巡回微分の回転不変性と、cut次数1での
  \(\Phi=\sum_{\rho\in C}[\rho\partial_\rho\Phi]\)。
- 正の次数を下げるHilbert漸化式の一意性、およびquadratic型の数値解
  \(h_m=\binom{m+2}{2}\)と二次式による増大上界。
- 本物のテンソル積による(3,3,3)係数表示、cut関係への線形同型、27次元性。
- 三角形箙のcut次数1の閉路が長さ3を持つこと。

次の結果は**条件付きの中間補題**です。

- 正次数成分の分解が与えられた場合の生成の帰納法。
- Extの次元表が有限台を持ち、指定の一項が1である場合の数値条件の帰結。
- coherentな有限区間同型が与えられた場合の大域的な周期同型の構成。
- 完全忠実な線形関手と対象同型が与えられた場合の、Homの積を保つ共役。

AS正則性からこれらの入力を導く部分は未証明です。
詳細は[STATUS.md](STATUS.md)、[GAPS.md](GAPS.md)、[HANDOFF.md](HANDOFF.md)を参照して下さい。

## 再現

Lean 4.24.0とmathlib v4.24.0を使います。依存コミットは`lake-manifest.json`に固定しています。

```bash
lake exe cache get
./scripts/check.sh
```

`lake exe cache get`は依存ライブラリのコンパイル済みファイルの取得であり、
本プロジェクトの証明を検証するコマンドは`lake build`と公理依存監査です。

初めて展開した環境で依存が解決されない場合は、次を実行して下さい。

```bash
lake update
lake exe cache get
./scripts/check.sh
```

`ASGinzburg.lean`は全モジュールをimportします。
`AxiomAudit.lean`は全161宣言に対して`#print axioms`を実行します。
許される依存はLeanの標準的な`propext`、`Classical.choice`、`Quot.sound`だけです。
数値計算は証明タクティクで行い、`native_decide`を使っていません。

## 含まれる検証記録

- `verification/build.log`：全ターゲットの成功記録。
- `verification/axioms.log`：全宣言の公理依存。
- `verification/declarations.json`：宣言名とソース位置。
- `verification/results.json`：バージョン、ソースハッシュ、検証結果。
- `docs/source.pdf`：今回の入力論文の同一バイト列。

**ビルド成功は、ここに実装した補題の検証を意味します。主定理の完成を意味しません。**
