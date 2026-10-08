# 射影対象・単純商・Extと原論文の対応

原論文PDF §1.2 (1.5)–(1.7)を再読した上で、既存の線形presheafモデルを保って実装した。
`A.Hom u v=e_vAe_u`、右作用は`M_v×A.Hom u v→M_u`。周期性を追加仮定にしていない。

| 原論文／必要な構造 | 実装と証明 | 利用先 |
|---|---|---|
| P_v=e_vA | 既存representable v。全Mに対するrepresentableYonedaEquiv、生成元からの逆写像 | 射影性と実際のHom計算 |
| P_vの射影性 | epiの成分全射性とYonedaの自然性からProjective | 四項分解の各項、Ext計算 |
| 十分な射影対象 | 全M_iの全要素で添字付けたrepresentableの直和と全射 | mathlibの標準projective resolution・HasExt |
| P_v A_{>0} | representableRadical。u<vなら全A.Hom u v、他は零。positiveActionSpanとの一致を証明 | s_vとminimalityの基盤 |
| s_v=P_v/P_v A_{>0} | radical包含の実際のcokernel。対角1次元・他の成分IsZero。Simpleを証明 | (1.6)の分解対象 |
| 短完全列 | RightSubmodule.quotientShortExact | 分解・次元シフト |
| 射影分解 | ProjectiveResolution.ofを既存RightModuleに適用。正次数exactness | 一般の標準分解 |
| 実際のExt | HasExt.{v}を証明し、derived-category Abelian.Extを使用 | 後続のHom複体との比較 |
| Ext⁰(P_i,M) | addEquiv₀と線形Yonedaから加法的同型M_i | 次元条件の初期次数 |
| Extⁿ⁺¹(P_i,M)=0 | mathlib Ext.eq_zero_of_projective | 射影対象に関する標準消滅 |

radicalの閉性では、u<vの成分からu以上の成分へ作用する射が零になるpositive条件を使う。
positiveActionSpanの一致の順方向ではP_vのid_vと任意の正次数成分を掛ける。
逆方向ではv以下の成分でなければ生成元となるP_vの成分がpositive条件で零。
商の単純性は、対角の1次元vector spaceのSimpleと、他の成分の消滅からmonoを成分ごとに判定する。

利用した固定mathlibの主要API：

- CategoryTheory.Preadditive.Projective.Basic：Projective、直和の射影性、EnoughProjectives。
- CategoryTheory.Abelian.Exact：ShortComplex.exact_cokernel。
- Algebra.Category.ModuleCat.Simple：simple_of_finrank_eq_one。
- CategoryTheory.Abelian.Projective.Resolution：ProjectiveResolution.of。
- Algebra.Homology.DerivedCategory.Ext.EnoughProjectives：hasExt_of_enoughProjectives、Ext.eq_zero_of_projective。
- Algebra.Homology.DerivedCategory.Ext.Basic：実際のAbelian.ExtとExt.addEquiv₀。

これらのinstanceは既存の対象と実際の構成から証明した標準クラスであり、外部axiomや任意Propによる置換ではない。
標準分解は無限であり得る。(1.6)の有限四項、微分、minimality、AS条件はまだ実装していない。
全高次Extのk作用と線形性、Hom複体による計算・(1.7)の次元条件は未実装。
Extの第1引数P_iが射影対象である消滅は、原論文で第2引数がP_vであるExt(s_u,P_v)のAS条件と異なる。
presheafと局所単位元付き直和加群の明示的同値も残る。
主定理の代数閉・標数0の仮定を弱めたとは扱わず、定理3.2・系5.2は未証明で形式的な文も未実装。
