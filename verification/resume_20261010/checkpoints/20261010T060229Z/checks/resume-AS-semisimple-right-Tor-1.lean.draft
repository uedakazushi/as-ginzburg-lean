import work.ASGinzburgDraft.ASCutSemisimpleRightResolution
import ASGinzburg.BalancedTensorTorLeft

/-! From the original AS condition, the actual graded radical quotient
has zero ordinary first-factor Tor in degrees at least four against every
left module. The proof computes the actual derived tensor on its finite
projective resolution. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem ASRegular.cutSemisimpleRightTor_isZero_ge_four
    (hAS : A.ASRegular Q) (N : ModuleCat.{v} (hAS.CutGradedAlgebra A Q))
    (n : ℕ) :
    IsZero ((balancedTensorTorLeftFunctor.{u,v,v,v} k
      (hAS.CutGradedAlgebra A Q) N (n+4)).obj
        (hAS.cutSemisimpleRightObject A Q)) :=
  balancedTensorTorLeft_isZero_of_resolution_term k (hAS.CutGradedAlgebra A Q)
    N (hAS.cutSemisimpleRightObject A Q)
    (hAS.cutSemisimpleRightProjectiveResolution A Q) (n+4)
    (hAS.cutSemisimpleRightProjectiveResolution_isZero_ge_four A Q n)

end ASGinzburg.ZAlgebra
