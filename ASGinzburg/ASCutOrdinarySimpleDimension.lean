import ASGinzburg.ASCutOrdinaryResolutions
import ASGinzburg.ModuleCatHomUniverseExt
import ASGinzburg.FourTermProjectiveDimension

/-! Genuine ordinary vertex modules have projective dimension at most
three and actual Ext vanishes in every degree at least four, against
every ordinary right-R target. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

instance ASRegular.cutOrdinarySimple_hasProjectiveDimensionLE_three
    (hAS : A.ASRegular Q) (x : Q.LiftVertex) :
    HasProjectiveDimensionLE (hAS.cutOrdinarySimple A Q x) 3 :=
  fourTermProjectiveResolution_hasProjectiveDimensionLE
    (hAS.cutOrdinarySimpleProjectiveResolution A Q x)
    (hAS.cutOrdinarySimpleProjectiveResolution_isZero_ge_four A Q x 0)

theorem ASRegular.cutOrdinarySimple_ext_ge_four_eq_zero (hAS : A.ASRegular Q)
    (x : Q.LiftVertex) (N : ModuleCat.{v} (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ) (n : ℕ)
    (e : Abelian.Ext.{v} (hAS.cutOrdinarySimple A Q x) N (n+4)) : e=0 :=
  e.eq_zero_of_hasProjectiveDimensionLT 4 (by omega)

end ASGinzburg.ZAlgebra
