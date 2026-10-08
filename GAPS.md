# 今回のRightModuleのAbelian構造・ホモロジー接続

2026年10月8日。ユーザーの再開指示により、AS側の最初の課題を既存のpresheafモデル上で完成。
極限・余極限の閉性、核・余核・有限積、Abelian構造、成分homology、exactnessの像＝核判定、
短完全列・mono/epi・injective/surjectiveの成分判定を実装しました。
Lean 4.24.0と固定mathlibで全202宣言の監査・ビルドは終了0。未解決の実装エラーはありません。
原論文との対応とmathlibの利用先は`docs/rightmodule_homological_bridge.md`を参照。
今回の補題には原論文から導出する未証明のAS仮定を追加していません。

以下の未完了課題を進めるには別の明示的な指示が必要です。
原論文を否定する反例や矛盾を発見したという記録はありません。
旧回収記録はcheckpoints/とrecovery/に無変更で保存しています。

# 未完了部分と、主定理を完成させるための証明義務

## 現在の障害

主定理は未完成です。数学的な反例を見つけたわけではありません。
原論文の証明には、ここで実装した組合せ・線形代数より大きなホモロジー代数の構築が必要です。
現時点ではAS正則性とGinzburg正則性の本体をLeanで定義しておらず、両者の同値を述べる型もありません。
この欠落を任意の`Prop`で置き換えたり、主定理に等しい仮定を追加したりしていません。

Lean 4.24.0のmathlibソースには、一般のAbelian圏のExt、導来圏、projective resolutionは存在します。
したがって「LeanにExtがない」ことは障害ではありません。
既存の線形右加群圏はAbelianになり、mathlibの核・余核・ShortComplex.homologyとexactnessへ接続済みです。
次は射影対象・実際の分解とExt計算の接続が必要です。
取得したmathlibのファイル名検索では、AS正則性、Ginzburg dg代数、Calabi–Yau completion、
高次preprojective代数をそのまま使える専用の実装を確認できませんでした。
これは全宣言を意味論的に検索した不存在証明ではありません。

## 1. AS側の定義と最小射影分解

次の作業を最優先にします。

1. **完成**：`ZAlgebra.RightModule`のAbelian構造、核・余核の閉性と成分同型、
   mathlibのhomologyとexactness・短完全列の成分判定。
   `rightModuleProperty`の加法性・k線形性は既存の定義のまま。
2. **完成**：任意のMについて線形Yoneda評価同型と`representable v`の射影性。
   `rightModule_epi_iff_surjective`を用いてdistinguished generatorを持ち上げる。
   representableの直和によるEnoughProjectivesも完成。有限・最小の分解は未証明。
3. 正次数radical submoduleと単純加群s_vを定義する。
4. 原論文(1.6)の四項の有限直和と微分を実際の対象として定義する。
5. 完全性と最小性を定義し、(1.7)を本物のExtの次元で定式化する。

presheafモデルと`⊕_v M_v`の局所単位元付き右加群の明示的同値は未実装です。
原論文§1.2との右作用の向きは照合済みですが、Extを比較する形式的同値の代わりにはしません。

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
