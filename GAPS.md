# 現在までに完成したAS側の基盤

有限coproductのHomと余極限の自然な交換を追加しました（FiniteCoproductHomColimits）。
AS分解の第1・第2項と実際のExt⁰にも適用済みです。高次Extの直和交換とGr(A)比較は未証明です。
最新ローカル検証 20261008T050918Z-e404c546：52数学モジュール・517異なる宣言・224 theorem、全段階終了0。
単位1の差分・実測時刻・次の義務はRECENT_RUN.mdとruns/ext-sums-20261008.md。

2026年10月8日。既存の線形RightModuleを保ち、有限AS分解だけから全次数のExt(s_w,P_i)の有限性と次数4以上の消滅を証明しました。
有限AS分解の存在の下で、元のASRegularと式(1.11)の数値条件の両方向の同値が証明済みです。
具体的な左加群・A-dual・左単純商を構成し、実際のExt(s_w,P_i,p)の成分左加群が
p≠3で零、p=3でs^left_(tau^{-1}w)に同型であることを左作用ごと証明しました。
Hom(P_i,-)・Ext⁰(P_i,-)の余極限交換、左側の射影性・EnoughProjectives・実際のExtの存在も完成しました。
左A-dualも構成し、左右のrepresentableが二重A-dualで元に戻る同型を証明しました。
原論文のExt(s_w,A)への直和交換、Gr(A)比較、周期性と主定理は未証明です。

52数学モジュール、517異なる明示的宣言、224 theorem、98 named instanceのビルド・公理監査は終了0。
定理3.2・系5.2は**未証明、形式的な定理文も未実装**です。
任意のAでAS分解の存在を証明したとは扱わない。原論文Gr(A)との明示的同値も未実装。
未解決のコンパイルエラーなし。原論文に反例・矛盾を発見したという記録なし。
最新ユーザー指示により自律的に継続し、検証済み単位を直接mainへ保存する。
旧版・入力PDF・回収記録は無変更。

# 未完了部分と、主定理を完成させるための証明義務

## 現在の障害

主定理は未完成です。数学的な反例を見つけたわけではありません。
原論文の証明には、ここで実装した組合せ・線形代数より大きなホモロジー代数の構築が必要です。
既存presheafモデル上のAS正則性は、原論文(1.6)の有限最小分解の存在と
実際のAbelian.Extの総Module.rank=1により具体的に定義しました。
Ginzburg正則性の本体と両者の同値を述べる型は未実装です。
この欠落を任意の`Prop`で置き換えたり、主定理に等しい仮定を追加したりしていません。

Lean 4.24.0のmathlibソースには、一般のAbelian圏のExt、導来圏、projective resolutionは存在します。
したがって「LeanにExtがない」ことは障害ではありません。
既存の線形右加群圏はAbelianになり、mathlibの核・余核・ShortComplex.homologyとexactnessへ接続済みです。
射影性・EnoughProjectives・標準射影分解・実際のExtの存在も接続済みです。
有限最小分解データからmathlib ProjectiveResolutionへの変換と実際Extのk線形性は完成。
実際のsyzygy短完全列からExt³(s_(tau v),P_v)≃kと、AS条件による他の全Extの消滅まで完成。
Ext成分の左加群同型は完成。全次数の自然なHom複体–Ext比較、直和交換とGr(A)比較が必要です。
取得したmathlibのファイル名検索では、AS正則性、Ginzburg dg代数、Calabi–Yau completion、
高次preprojective代数をそのまま使える専用の実装を確認できませんでした。
これは全宣言を意味論的に検索した不存在証明ではありません。

## 1. AS側の定義と最小射影分解

1〜5は基盤として完成。次の優先課題は以下の6と§2の直和交換・双対性です。

1. **完成**：`ZAlgebra.RightModule`のAbelian構造、核・余核の閉性と成分同型、
   mathlibのhomologyとexactness・短完全列の成分判定。
   `rightModuleProperty`の加法性・k線形性は既存の定義のまま。
2. **完成**：任意のMについて線形Yoneda評価同型と`representable v`の射影性。
   `rightModule_epi_iff_surjective`を用いてdistinguished generatorを持ち上げる。
   representableの直和によるEnoughProjectivesも完成。任意のAについて有限・最小分解の存在は未証明。
3. **完成**：正次数の右積のspanと同定したradical、商s_v、対角1次元・他の成分零、単純性、短完全列。
4. **一般radicalの閉性・自然性と、微分の像がradicalに入るminimality・因子化判定は完成**。
   原論文(1.6)の四項の有限直和・微分・完全性・左端Mono・最小性をASResolutionとして定義済み。
   与えたASResolutionから実際のmathlib ProjectiveResolutionを構成し、augmentationのQuasiIsoを証明済み。
5. **完成**：実際の全高次Extのk作用、0次Homとの線形同型、
   (1.7)の全被覆頂点・全次数の総Module.rank条件によるASRegular定義。
   各Extの有限次元性とrank≤1もAS条件から証明済み。
   任意のAやJacobian代数でASRegularが成立することは未証明。
   命題1.3のdegree-three比較と、実際のExtのdelta型次元公式は証明済み。
   Ext成分の左作用と左単純商への同型は完成。全次数の自然な比較、直和交換とGr(A)比較は未証明。

6. **完成**：有限coproductの射影項のHomと直和の自然な交換。
   **次の実装単位**：実際のExtの接続写像・次元シフトの自然性と高次Extの直和交換。
   全次数の自然なHom複体–Ext比較、または長完全列の自然性から高次Extの交換へ移す。
   Hom(P_i,-)・Ext⁰(P_i,-)の交換は完成済み。

標準`ProjectiveResolution`と`HasExt.{v}`はEnoughProjectivesから完成しました。
`representableExtZeroLinearEquiv`は実際のExt⁰(P_i,M)とM_iの線形同型。
高次Ext(P_i,M)の消滅は射影対象が第1引数にあるためで、Ext(s_u,P_v)のAS条件ではありません。
標準分解は無限であり得るため、(1.6)の有限四項分解を得たと扱いません。
ASRegularから分解を選ぶことは定義(i)の存在条件を使います。周期性やdelta型Ext表を追加していません。
mathlibの古いleftDerived型ExtにはProjectiveResolution.isoExtがありますが、
今回使用する新しいAbelian.Extとの比較定理ではありません。両者を取り違えません。

presheafモデルと`⊕_v M_v`の局所単位元付き右加群の明示的同値は未実装です。
原論文§1.2との右作用の向きは照合済みですが、Extを比較する形式的同値の代わりにはしません。

代替ルートとして、成分の直和からnon-unital algebraを作り、そのunitizationの`ModuleCat`に
locally unitalな加群を埋め込むことが考えられます。
この場合もExtが元の加群圏のExtと一致することを証明してから使います。

`ZAlgebra.generated_of_decomposition`の仮定である成分分解を、d₁から導かなければなりません。
現在の補題は帰納法の段階だけを検証しており、命題1.2全体ではありません。

## 2. Ext双対性から周期性

1. **完成**：有限AS分解に実際のHom(-,P_v)を適用する複体。
2. **完成**：高い頂点のHom消滅からs_(τv)の0→0→0→kを得る。
3. **完成**：syzygy短完全列・実際の線形dimension shiftからExt³≃k。
   Hom cohomologyとのdegree-three線形同型も完成。一般の自然な比較は未証明。
4. **完成**：総Cardinal rank=1から他の全Extの消滅、実際のfinrank関数の有限台とFinsupp表。
   既存presheafモデルのASRegularから(1.11)の数値的順方向まで。
   逆方向も有限AS分解だけからExtの有限性を導いて証明済み。
5. 左右のA-dualとrepresentableの二重双対の対象同型は完成。
   一般の評価写像の自然性、有限生成projectiveへの拡張と有限射影性、perfect complexの二重双対は未証明。
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

今回の9単位はdocs/as_finiteness_left_duality.mdに原論文との対応・仮定・利用先を記載。
51数学モジュール・505宣言の最新検査とmain保存先はRECENT_RUN.md参照。
