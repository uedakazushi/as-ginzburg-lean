import work.ASGinzburgDraft.BalancedTensorEnvelopingTorComparison
import work.ASGinzburgDraft.ASCutSemisimpleRightResolution

/-! From the original AS condition, the genuine enveloping Tor of the
actual semisimple right quotient tensored with any ordinary left module
vanishes in degrees at least four. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

attribute [local instance] regularEnvelopingModule regularEnvelopingScalarTower

noncomputable def ASRegular.cutSemisimpleEnvelopingTensorObject
    (hAS : A.ASRegular Q) (N : ModuleCat.{v} (hAS.CutGradedAlgebra A Q)) :
    ModuleCat.{v} (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))ᵐᵒᵖ :=
  (((tensorRightEnvelopingBifunctor k (hAS.CutGradedAlgebra A Q)).obj
    (hAS.cutSemisimpleRightObject A Q)).obj N)

theorem ASRegular.cutSemisimpleEnvelopingTor_isZero_ge_four
    (hAS : A.ASRegular Q) (N : ModuleCat.{v} (hAS.CutGradedAlgebra A Q)) (n : ℕ) :
    IsZero ((balancedTensorTorLeftFunctor.{u,v,v,v} k
      (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))
      (hAS.CutGradedAlgebra A Q) (n + 4)).obj
        (hAS.cutSemisimpleEnvelopingTensorObject A Q N)) :=
  balancedTensorEnvelopingTor_isZero_of_resolution_term k (hAS.CutGradedAlgebra A Q)
    (hAS.cutSemisimpleRightProjectiveResolution A Q) (ProjectiveResolution.of N) (n + 4)
    (hAS.cutSemisimpleRightProjectiveResolution_isZero_ge_four A Q n)

end ASGinzburg.ZAlgebra
