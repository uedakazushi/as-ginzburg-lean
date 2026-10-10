import ASGinzburg.BalancedTensorTorBalanceConsequences
import ASGinzburg.ASCutSemisimpleTorFinite
import ASGinzburg.ASCutSemisimpleRightTor

/-! The actual second-factor derived tensor inherits bounded vanishing
and field finiteness from the AS semisimple right resolution, by the
proved same-ring balance rather than by an extra assumption. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem ASRegular.cutSemisimpleSecondTor_isZero_ge_four
    (hAS : A.ASRegular Q) (N : ModuleCat.{v} (hAS.CutGradedAlgebra A Q)) (n : ℕ) :
    IsZero ((balancedTensorTorFunctor.{u,v,v,v} k (hAS.CutGradedAlgebra A Q)
      (hAS.cutSemisimpleRightObject A Q) (n+4)).obj N) :=
  balancedTensorTor_isZero_of_right_resolution_term k (hAS.CutGradedAlgebra A Q)
    (hAS.cutSemisimpleRightObject A Q) N
    (hAS.cutSemisimpleRightProjectiveResolution A Q) (n+4)
    (hAS.cutSemisimpleRightProjectiveResolution_isZero_ge_four A Q n)

theorem ASRegular.cutSemisimpleSecondTor_finite
    (hAS : A.ASRegular Q) (N : ModuleCat.{v} (hAS.CutGradedAlgebra A Q))
    [Module.Finite k N] (n : ℕ) :
    Module.Finite k ((balancedTensorTorFunctor.{u,v,v,v} k
      (hAS.CutGradedAlgebra A Q) (hAS.cutSemisimpleRightObject A Q) n).obj N) := by
  letI := hAS.cutSemisimpleRightProjectiveResolution_finite A Q n
  exact balancedTensorTor_finite_of_right_resolution_term k (hAS.CutGradedAlgebra A Q)
    (hAS.cutSemisimpleRightObject A Q) N
    (hAS.cutSemisimpleRightProjectiveResolution A Q) n

theorem ASRegular.cutSemisimpleBalancedTor_finite (hAS : A.ASRegular Q) (n : ℕ) :
    Module.Finite k ((balancedTensorTorFunctor.{u,v,v,v} k
      (hAS.CutGradedAlgebra A Q) (hAS.cutSemisimpleRightObject A Q) n).obj
        (hAS.cutSemisimpleLeftObject A Q)) := by
  letI := hAS.cutSemisimpleLeftObject_finite A Q
  exact hAS.cutSemisimpleSecondTor_finite A Q (hAS.cutSemisimpleLeftObject A Q) n

end ASGinzburg.ZAlgebra
