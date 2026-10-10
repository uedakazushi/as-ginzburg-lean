import work.ASGinzburgDraft.BalancedTensorEnvelopingSecondTorComparison
import work.ASGinzburgDraft.ASCutSemisimpleEnvelopingTor
import work.ASGinzburgDraft.ASCutSemisimpleTorFinite

/-! The original AS condition controls the actual second-factor
enveloping derived tensor of its semisimple tensor module: it vanishes
above degree three and is finite over the field against the left
semisimple quotient in every degree. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

attribute [local instance] regularEnvelopingModule regularEnvelopingScalarTower

theorem ASRegular.cutSemisimpleEnvelopingSecondTor_isZero_ge_four
    (hAS : A.ASRegular Q) (N : ModuleCat.{v} (hAS.CutGradedAlgebra A Q)) (n : ℕ) :
    IsZero ((balancedTensorTorFunctor.{u,v,v,v} k
      (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))
      (hAS.cutSemisimpleEnvelopingTensorObject A Q N) (n+4)).obj
        (ModuleCat.of (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))
          (hAS.CutGradedAlgebra A Q))) :=
  balancedTensorEnvelopingSecondTor_isZero_of_resolution_term k
    (hAS.CutGradedAlgebra A Q) (hAS.cutSemisimpleRightProjectiveResolution A Q)
    (ProjectiveResolution.of N) (n+4)
    (hAS.cutSemisimpleRightProjectiveResolution_isZero_ge_four A Q n)

theorem ASRegular.cutSemisimpleEnvelopingSecondTor_finite
    (hAS : A.ASRegular Q) (N : ModuleCat.{v} (hAS.CutGradedAlgebra A Q))
    [Module.Finite k N] (n : ℕ) :
    Module.Finite k ((balancedTensorTorFunctor.{u,v,v,v} k
      (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))
      (hAS.cutSemisimpleEnvelopingTensorObject A Q N) n).obj
        (ModuleCat.of (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))
          (hAS.CutGradedAlgebra A Q))) := by
  letI := hAS.cutSemisimpleRightProjectiveResolution_finite A Q n
  exact balancedTensorEnvelopingSecondTor_finite_of_resolution_term k
    (hAS.CutGradedAlgebra A Q) (hAS.cutSemisimpleRightProjectiveResolution A Q)
    (ProjectiveResolution.of N) n

theorem ASRegular.cutSemisimpleEnvelopingBalancedTor_finite
    (hAS : A.ASRegular Q) (n : ℕ) :
    Module.Finite k ((balancedTensorTorFunctor.{u,v,v,v} k
      (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))
      (hAS.cutSemisimpleEnvelopingTensorObject A Q (hAS.cutSemisimpleLeftObject A Q)) n).obj
        (ModuleCat.of (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))
          (hAS.CutGradedAlgebra A Q))) := by
  letI := hAS.cutSemisimpleLeftObject_finite A Q
  exact hAS.cutSemisimpleEnvelopingSecondTor_finite A Q
    (hAS.cutSemisimpleLeftObject A Q) n

end ASGinzburg.ZAlgebra
