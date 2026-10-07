# 回収時点の障害追記

今回、新しい数学的検討やLean形式化は行っていません。

- 環境：Lean／lake、依存パッケージ、コンパイルキャッシュが回収先にありません。現在のエラーはlake: command not found（終了127）。Leanファイルの型エラーは今回観測できていません。
- 監査：scripts/audit_sources.pyの宣言名正規表現がドットを処理せず、InWindow.monoをInWindowとして列挙しています。個別公理監査の完全性に1件の穴があります。ソースと旧ログは保存したままです。
- 回収：35ファイルのチェックポイントは回収済み。過去の全操作履歴・削除済み一時ファイル・Git履歴はそのzipからは回収できません。
- 主要な数学・実装の不足：AS正則性とGinzburg正則性の定義、実際のExt・最小射影分解との接続、Ext双対性からの区間同型、Jacobian商・dg微分とd²=0、外部一般定理、同型類の全単射。
- 原論文を否定する数学的反例や矛盾が見つかったという記録はありません。以下は実装不足・未証明の証明義務です。

# 未完了部分と、主定理を完成させるための証明義務

## 現在の障害

主定理は未完成です。数学的な反例を見つけたわけではありません。
原論文の証明には、ここで実装した組合せ・線形代数より大きなホモロジー代数の構築が必要です。
現時点ではAS正則性とGinzburg正則性の本体をLeanで定義しておらず、両者の同値を述べる型もありません。
この欠落を任意の`Prop`で置き換えたり、主定理に等しい仮定を追加したりしていません。

Lean 4.24.0のmathlibソースには、一般のAbelian圏のExt、導来圏、projective resolutionは存在します。
したがって「LeanにExtがない」ことは障害ではありません。
今回定義した、局所単位元を持つZ-代数の**線形右加群圏との接続**がまず必要です。
取得したmathlibのファイル名検索では、AS正則性、Ginzburg dg代数、Calabi–Yau completion、
高次preprojective代数をそのまま使える専用の実装を確認できませんでした。
これは全宣言を意味論的に検索した不存在証明ではありません。

## 1. AS側の定義と最小射影分解

次の作業を最優先にします。

1. `ZAlgebra.RightModule`のAbelian構造を与える。
   現在はk線形presheafのfull subcategoryを定義した段階で、核・余核・exactnessの閉性は未証明。
2. `representable v`の射影性を証明する。
3. 正次数radical submoduleと単純加群s_vを定義する。
4. 原論文(1.6)の四項の有限直和と微分を実際の対象として定義する。
5. 完全性と最小性を定義し、(1.7)を本物のExtの次元で定式化する。

代替ルートとして、成分の直和からnon-unital algebraを作り、そのunitizationの`ModuleCat`に
locally unitalな加群を埋め込むことが考えられます。
この場合もExtが元の加群圏のExtと一致することを証明してから使います。

`ZAlgebra.generated_of_decomposition`の仮定である成分分解を、d₁から導かなければなりません。
現在の補題は帰納法の段階だけを検証しており、命題1.2全体ではありません。

## 2. Ext双対性から周期性

1. 有限生成のprojective resolutionにHom(-,P_v)を適用する。
2. `representableHom_vanishes`を使い、s_(τv)について0→0→0→kの複体を得る。
3. そのtop cohomologyを実際のExt³と同定する。
4. Ext次元の台が有限であることを示し、`dimension_table_eq_single`を適用する。
5. 有限生成projectiveのA-dual、perfect complexの二重双対を構成する。
6. 有限長加群に対しExtの次数3への集中と完全反変同値を証明する。
7. N=D Ext³(-,A)の有限区間への制限と、projective coverを保つことを証明する。
8. coverから正規化した区間同型を作り、区間包含に対するcoherenceを証明する。

最後の8が済めば`WindowSystem.periodIso`に渡せます。
**WindowSystemを与えること自体をAS正則性の定義に追加してはいけません。**
周期性を仮定せず導くことがこの論文の重要な部分です。

## 3. ポテンシャル、Jacobian代数、Ginzburg dg代数

1. 閉じた可合成道の巡回空間と、今のcyclic word空間の適切な部分空間を同定する。
2. 巡回微分が正しい始点・終点を持つ道に入ることを証明する。
3. Jacobianイデアル、商代数、cut gradingによるunrollingを構成する。
4. 拡張箙上のgraded path algebraを定義する。
5. 微分を生成元からsigned Leibniz則で延長し、d²=0を証明する。
6. そのコホモロジーを使ってGinzburg正則性を定義する。

現在の`GinzburgGrading`は生成元と次数だけです。dg代数を完成したものとして使えません。
`cut_cyclic_derivative_identity`は(3.8)の実際の巡回恒等式ですが、
Jacobian代数から最小関係の基底が得られることは別の未証明事項です。

## 4. 論文§2の外部一般定理

以下を証明済みのmathlib定理に帰着するか、新たに形式化する必要があります。

| 原論文で使う結果 | 必要な形式化 |
|---|---|
| Reyes–Rogalski：(2.1)–(2.3) | generalized AS regularとgraded twisted CY、smoothness、可逆双加群、Nakayama twist |
| Hanihara：(2.4)–(2.6) | perfect/finite-dimensional商圏、tilting equivalence、Serre functor、parameter 1、2-representation infiniteness |
| Herschend–Iyama–Oppermann：(2.7)–(2.8) | inverse dualizing complex、derived tensor algebra、そのH⁰と積 |
| Keller：(2.10)、c=0 | relation-extensionのGinzburg dg代数との擬同型 |
| Ginzburg：逆向き | 負次数acyclicityから標準双加群分解の完全性と3-CY双対性 |

`Conjugation.conjugateHom_comp`は、これらを経て得たHom同定が積を保つことを検証する補題です。
tiltingやCY completionそのものの代わりではありません。

原論文の引用定理を`axiom`として置けば形式的な骨組みは短く書けますが、
それを「主結果のLean証明」とは扱いません。

## 5. 同型類の全単射と選択の独立性

上記の構築後、次を残さず証明する必要があります。

- 頂点固定の代数同型の関係と、cut gradingを保つ道代数自己同型の関係。
- 二つの対応が各関係を保ち、商に降りること。
- foundation制限、最小関係の基底・代表元の選択からの独立性。
- 代表元変更を吸収する三角的な矢の置換が可逆であること。
- 周期同型を付加データとしていないことと、その選択からの独立性。
- 両合成がそれぞれの同型類において恒等となること。

現在、これらを仮定する抽象的な全単射定理は作っていません。

## 6. del Pezzo増大度とquadratic系

`positive_recurrence_unique`はHilbert関数がEuler式を満たすことを仮定します。
exact resolutionから(4.2)を導き、del Pezzo模型の多項式増大を証明して初めて§4全体が完成します。

三角形箙のcut閉路がcubicに限られること、三重テンソル積の係数表示は証明済みです。
しかし周期性とAS–Ginzburg対応が未証明なので、命題5.1と系5.2は導けません。
同じ次数の矢の像が長さ1に限られる補題から、自己同型群が三つのGLの積であることも仕上げる必要があります。
