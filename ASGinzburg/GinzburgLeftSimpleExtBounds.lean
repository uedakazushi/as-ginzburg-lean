import ASGinzburg.GinzburgLeftFiniteProjectiveResolution
import ASGinzburg.FourTermProjectiveDimension
import ASGinzburg.LeftModuleExt

/-! Genuine Ginzburg regularity alone gives projective dimension at most
three and actual higher Ext vanishing for every original left simple. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem GinzburgRegular.leftSimple_hasProjectiveDimensionLE {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (i : ℤ) :
    HasProjectiveDimensionLE ((Q.unrolledJacobianZAlgebra k φ).simpleLeftModule i) 3 :=
  fourTermProjectiveResolution_hasProjectiveDimensionLE
    (h.leftSimpleProjectiveResolution Q k i)
    (h.leftSimpleProjectiveResolution_isZero_ge_four Q k i 0)

theorem GinzburgRegular.leftSimple_ext_ge_four_eq_zero {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (i : ℤ)
    (N : (Q.unrolledJacobianZAlgebra k φ).LeftModule) (n : ℕ)
    (e : Abelian.Ext.{u} ((Q.unrolledJacobianZAlgebra k φ).simpleLeftModule i) N (n+4)) :
    e=0 := by
  letI := h.leftSimple_hasProjectiveDimensionLE Q k i
  exact e.eq_zero_of_hasProjectiveDimensionLT 4 (by omega)

end ASGinzburg.CutQuiver
