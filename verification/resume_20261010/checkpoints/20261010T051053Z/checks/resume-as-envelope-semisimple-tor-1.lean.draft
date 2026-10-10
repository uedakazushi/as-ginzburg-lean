import work.ASGinzburgDraft.AlgebraEnvelopingQuotientRightComparison
import work.ASGinzburgDraft.ASCutEnvelopingQuotient
import work.ASGinzburgDraft.ASCutSemisimpleEnvelopingSecondTor
import work.ASGinzburgDraft.BalancedTensorTorObjectComparison
import ASGinzburg.ASCutSemisimpleRightTor

/-! Actual second-factor enveloping Tor of the actual semisimple
kernel quotient against the regular bimodule is finite over the field
in every degree and zero above degree three, from the original AS
condition. The genuine quotient-module isomorphism supplies the transfer. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

attribute [local instance] regularEnvelopingModule regularEnvelopingScalarTower

noncomputable def ASRegular.cutEnvelopingSemisimpleRightObject (hAS : A.ASRegular Q) :
    ModuleCat.{v} (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))ᵐᵒᵖ :=
  idealQuotientRightObject (hAS.cutEnvelopingAugmentationKernel A Q)

noncomputable def ASRegular.cutEnvelopingSemisimpleRightTensorIso
    (hAS : A.ASRegular Q) :
    hAS.cutEnvelopingSemisimpleRightObject A Q ≅
      hAS.cutSemisimpleEnvelopingTensorObject A Q (hAS.cutSemisimpleLeftObject A Q) :=
  (quotientTensorRightKernelIso k (hAS.CutGradedAlgebra A Q)
    (hAS.cutGradedRadical A Q)).symm

set_option maxHeartbeats 800000 in
noncomputable def ASRegular.cutEnvelopingSemisimpleTorIso
    (hAS : A.ASRegular Q) (n : ℕ) :
    (balancedTensorTorFunctor.{u,v,v,v} k
      (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))
      (hAS.cutEnvelopingSemisimpleRightObject A Q) n).obj
        (ModuleCat.of (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))
          (hAS.CutGradedAlgebra A Q)) ≅
      (balancedTensorTorLeftFunctor.{u,v,v,v} k (hAS.CutGradedAlgebra A Q)
        (hAS.cutSemisimpleLeftObject A Q) n).obj (hAS.cutSemisimpleRightObject A Q) :=
  (balancedTensorTorFirstObjectIso k
    (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))
    (hAS.cutEnvelopingSemisimpleRightTensorIso A Q) n).app
      (ModuleCat.of (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))
        (hAS.CutGradedAlgebra A Q)) ≪≫
  balancedTensorEnvelopingSecondTorComparisonIso k (hAS.CutGradedAlgebra A Q)
    (hAS.cutSemisimpleRightProjectiveResolution A Q)
    (ProjectiveResolution.of (hAS.cutSemisimpleLeftObject A Q)) n

theorem ASRegular.cutEnvelopingSemisimpleTor_isZero_ge_four
    (hAS : A.ASRegular Q) (n : ℕ) :
    IsZero ((balancedTensorTorFunctor.{u,v,v,v} k
      (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))
      (hAS.cutEnvelopingSemisimpleRightObject A Q) (n+4)).obj
        (ModuleCat.of (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))
          (hAS.CutGradedAlgebra A Q))) :=
  IsZero.of_iso (hAS.cutSemisimpleRightTor_isZero_ge_four A Q
    (hAS.cutSemisimpleLeftObject A Q) n) (hAS.cutEnvelopingSemisimpleTorIso A Q (n+4))

set_option maxHeartbeats 800000 in
theorem ASRegular.cutEnvelopingSemisimpleTor_finite
    (hAS : A.ASRegular Q) (n : ℕ) :
    Module.Finite k ((balancedTensorTorFunctor.{u,v,v,v} k
      (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))
      (hAS.cutEnvelopingSemisimpleRightObject A Q) n).obj
        (ModuleCat.of (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))
          (hAS.CutGradedAlgebra A Q))) := by
  haveI : Module.Finite k ((balancedTensorTorLeftFunctor.{u,v,v,v} k
      (hAS.CutGradedAlgebra A Q) (hAS.cutSemisimpleLeftObject A Q) n).obj
        (hAS.cutSemisimpleRightObject A Q)) := hAS.cutSemisimpleTor_finite A Q n
  let e := hAS.cutEnvelopingSemisimpleTorIso A Q n
  exact Module.Finite.equiv e.toLinearEquiv.symm

end ASGinzburg.ZAlgebra
