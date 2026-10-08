# 線形右加群とホモロジー代数の接続

## 原論文と既存定義の対応

`docs/source.pdf` §1.2、(1.4)–(1.5)では `A_vu = e_v A e_u`、
`Gr(A)` は局所単位元を持つ右加群の圏、`P_v = e_v A` である。
右乗法は `M_v × A_vu → M_u` を与える。
`ZAlgebra.Hom u v` と `A.Obj` の射 `u → v` はこの `A_vu` に対応し、
`RightModule` は `A.Objᵒᵖ ⥤ ModuleCat k` の加法的・k線形関手のfull subcategoryである。
関手の反変性が右作用の向きと一致し、`representable v` の成分は `A.Hom u v` となる。
既存の `representableHomEquiv` は論文(1.5)のHom同定に対応する。

この実装では既存の `rightModuleProperty := F.Additive ∧ F.Linear k` を保つ。
各頂点の成分を持つ表現から直和 `⊕_v M_v` と局所単位元付き右作用を作る
明示的な同値は未実装である。以下は既存のpresheafモデル上の圏論的構築であり、
その同値や論文のExt双対性を証明したと主張するものではない。

原論文は代数閉体・標数0を固定しているが、今回の圏論的補題には一般の体で十分である。
これは補題の一般性であり、AS–Ginzburg主定理の仮定を弱める変更ではない。
正有向性・connected・有限次元性・AS条件・周期性をこの構築の追加仮定にはしない。

## 実装方針とmathlibの利用箇所

1. 極限の射影は各頂点でjointly monicである。自然性と図式の各関手の加法性・線形性から、
   極限関手の `map_add` と `map_smul` を導く。余極限はjointly epicな包含射で双対に示す。
2. `Limits.FullSubcategory` の
   `hasLimitsOfShape_of_closedUnderLimits` と双対の定理で(余)極限を持ち上げる。
   `createsLimitsOfShapeFullSubcategoryInclusion` と双対で包含がcreateすることを得る。
   存在する形状の(余)極限について証明し、特に有限積・核・余核を供給する。
3. `ModuleCat.Abelian` と `Abelian.FunctorCategory` によりambient関手圏はAbelian。
   `PreservesCoimageImageComparison.iso` により包含の下で余像→像の射が同型となる。
   full・faithfulな包含が同型を反映するので、
   `Abelian.ofCoimageImageComparisonIsIso` を既存の `RightModule` に適用する。
4. 包含と頂点評価が有限(余)極限を保存することから、mathlibの
   `Functor.PreservesHomology` と `ShortComplex` の実際のホモロジー・exactnessへ接続する。
   頂点ごとのホモロジーの消滅は全体の消滅を検出し、exactnessの成分判定を与える。
   `ShortComplex.moduleCat_exact_iff_range_eq_ker` で線形写像の像＝核に翻訳する。

## 次に必要な証明義務

上記4段階は既存のpresheafモデル上で完成した。公開した判定は
`rightModule_exact_iff_inclusion`、`rightModule_exact_iff`、
`rightModule_exact_iff_range_eq_ker`、`rightModule_shortExact_iff`、
`rightModule_mono_iff_injective`、`rightModule_epi_iff_surjective`である。
`rightModuleKernelObjIso`、`rightModuleCokernelObjIso`、`rightModuleHomologyObjIso`は
mathlibの普遍構成との実際の同型を与える。

2026-10-08の継続でrepresentableの射影性、EnoughProjectives、radical・単純商s_v、
標準projective resolutionと実際のExtの存在も完成した。
[対応と次の義務](rightmodule_projective_simple_bridge.md)参照。
残るのは(1.6)の有限最小分解、全Extのk線形性・Hom複体との比較、(1.7)の次元条件、
presheafモデルと直和・局所単位元付き右加群の明示的同値である。

今回の閉性の形状仮定はmathlibのModuleCatの有限(余)極限で満たされる。
原論文から新たに導出すべき数学的仮定を追加した条件付きAS補題は作らない。
定理3.2・系5.2の形式的定理文、命題1.4のAS条件からの周期性、命題5.1は依然として未証明である。
