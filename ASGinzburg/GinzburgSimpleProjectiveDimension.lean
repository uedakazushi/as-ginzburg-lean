import ASGinzburg.GinzburgASProjectiveResolution
import ASGinzburg.FourTermProjectiveResolutionExt

/-! Genuine Ginzburg regularity implies projective dimension at most
three and vanishing of the actual higher Ext of every right simple. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem GinzburgRegular.simple_ext_ge_four_eq_zero {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (v : Q.LiftVertex)
    (N : (Q.unrolledJacobianZAlgebra k φ).RightModule) (n : ℕ)
    (e : Abelian.Ext.{u} ((Q.unrolledJacobianZAlgebra k φ).simpleRightModule (Q.height v))
      N (n+4)) : e=0 :=
  (Q.unrolledJacobianZAlgebra k φ).rightFourTermProjectiveResolution_ext_ge_four_eq_zero
    (h.simpleProjectiveResolution Q k v)
    (h.simpleProjectiveResolution_isZero_ge_four Q k v 0) N n e

theorem GinzburgRegular.simple_hasProjectiveDimensionLE {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (v : Q.LiftVertex) :
    HasProjectiveDimensionLE
      ((Q.unrolledJacobianZAlgebra k φ).simpleRightModule (Q.height v)) 3 :=
  (Q.unrolledJacobianZAlgebra k φ).rightFourTermProjectiveResolution_hasProjectiveDimensionLE
    (h.simpleProjectiveResolution Q k v)
    (h.simpleProjectiveResolution_isZero_ge_four Q k v 0)

end ASGinzburg.CutQuiver
