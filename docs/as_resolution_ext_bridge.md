# AS有限最小分解と実際のExtへの接続

2026-10-08。原論文docs/source.pdfの§1.2、定義1.1、命題1.3を再読して実装した。
既存ZAlgebra.RightModuleは加法的・k線形な反変ModuleCat presheafのfull subcategoryのままである。
以下の構成はこの具体的圏で行う。原論文の局所単位元付き直和加群Gr(A)との明示的同値は未実装。

## 原論文と実装の対応

| 論文 | 実装 | 証明済み内容 |
|---|---|---|
| M A_{>0} | RightModuleRadical | 正次数右作用のspanの右作用閉性、module mapに対する自然性、線形functor |
| 最小微分 | RightModuleMinimality | 実際の像がradicalに入る条件、radical包含を通る因子化との同値、合成の閉性 |
| Hom(-,s_i)の零微分 | RightModuleSimpleHom | s_iの正次数radicalが零、最小微分のs_iへの合成が零 |
| (1.6)の有限最小分解 | ASResolution | incoming/outgoing有限添字、実際のcoproduct、射影性、微分、ShortComplex.Exact、左端Mono、minimality |
| 射影分解 | ASResolutionComplex | degree≥4の零、正次数exactness、augmentationのQuasiIso、mathlib ProjectiveResolutionへの変換 |
| 実際のExtのk作用 | RightModuleExtLinear | 標準導来圏のlinear localization、既存Abelian.Extの加法群上のModule構造、Ext⁰の元のHom作用との一致 |
| 定義1.1(ii)、(1.7) | ASRegular | SECOND argument P_vを固定し、全p≥0・全被覆頂点uの実際のExtの総Module.rank=1 |
| 最小分解のHom複体 | ASResolutionHomComplex | 実際のHom空間とprecompositionのk線形写像、d²=0、Hom(-,s_i)の零微分とhomologyの同定 |
| 命題1.3のHom項 | ASDualityHomTerms | s_(tau v)の分解の最初の三項からP_vへのHomが零、最後の項のHomがk |
| 同じHom複体のcohomology | ASDualityHomCohomology | H³とkの線形同型、他の次数のIsZero、top finrank=1 |
| 実際のExtの長完全列 | RightModuleExtSequence | shift線形性、Yoneda積双線形性、connecting map、射影的中間項による正次数のdimension shift |
| syzygy短完全列 | ASResolutionSyzygies | 二つの実際のkernelへのcover、Epi、三つのShortExact |
| 命題1.3の非零Ext | ASDualityExt | 三段のdimension shiftから実際のExt³(s_(tau v),P_v)≃ₗ[k]k、rank=finrank=1 |
| (1.11)の数値的順方向 | ASDualityDimension | 他の全Extの消滅、実際のfinrankのdelta公式、証明した有限台のFinsupp表 |

## 仮定を追加していないこと

ASRegularは任意のPropの入力や既存数値表を代替定義として受け取らない。
ASResolutionの存在と、実際のAbelian.Extの総rankが1であることの連言である。
周期同型、WindowSystem、delta型のExt表、主定理と同等の結論は含めない。
tauは元のCutQuiverの頂点置換であり、代数自己同型を仮定しない。
微分や矢の基底は同型類の付加データにしない。分解の存在から必要時に選ぶ。

Module.finrankだけで定義すると無限次元の空間のfinrank=0により条件を弱める恐れがある。
したがって総次元はCardinal値のModule.rankで表した。
総rank=1から各実際のExtのrank≤1、Module.Finite、finrank≤1を証明した。
rank=0と実際のExtの全要素が零であることの同値も証明した。

一般のAについて有限AS分解やASRegularが成立するという主張はしていない。
ASResolutionを与えた定理は原論文定義(i)のデータを使う条件付き補題である。
この存在条件自体を特定のJacobian代数などで導く部分は未証明。
一般の体で成立する基盤補題は、主定理の代数閉・標数0の仮定を弱める変更ではない。

## 実際のExt計算に残る義務

mathlibには古いleftDerived型のExtと新しいderived-category Abelian.Extが併存する。
ProjectiveResolution.isoExtは前者の計算定理であり、後者の比較としてそのまま使わない。
今回定義したModule構造とAS条件は後者のAbelian.Extを使う。

実装した有限分解からHom複体0→0→0→kと、そのH³=kを得た。
さらに実際のkernelを使う三つのsyzygy短完全列を構成し、線形dimension shiftを合成して
実際のExt³(s_(tau v),P_v)≃kを証明した。0次shiftのHom消滅も高い頂点の射影項から導いた。
この二つのkとの同型を合成したdegree-three比較もある。全M,N・全次数の自然な一般比較は未証明。

ASの総Cardinal rank=1と、この実際の非零項から他の全Extが零であることを導いた。
実際のfinrankの関数が有限台を持つことを証明してFinsupp表を構成した。
その表の関数はExtのfinrankそのものであり、結論を定義に置き換えていない。
これは既存presheafモデルのASRegularからの(1.11)の数値的順方向である。
その後の継続で、有限AS分解だけからExtの全次数の有限性を導き、逆方向も証明した。
数値的同値、具体的左加群・A-dual、Ext成分左加群と左単純商の同型、
Hom(P_i,-)・Ext⁰(P_i,-)の余極限交換はdocs/as_finiteness_left_duality.md参照。
以下は未証明で、原論文の命題1.3全体を完成扱いにはしない。

1. 有限coproductの射影項のHomと直和の交換、全次数の自然なHom複体–Ext比較。
2. Extと⊕P_iの交換、原論文のExt(s_u,A)の左作用との比較、(1.12)全体。
3. 原論文Gr(A)との明示的同値と、その同値がExtを保つこと。
4. 有限長双対性、区間同型とcoherence、AS条件からの周期性。

原論文からこれらを導く部分はSTATUS.mdとGAPS.mdに未証明として記録する。
定理3.2・系5.2は未証明で、形式的な定理文も未実装のままである。

