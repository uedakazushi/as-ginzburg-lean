import ASGinzburg.BalancedTensorTorLeftFinite
import ASGinzburg.ASCutSemisimpleRightResolution
import ASGinzburg.AlgebraModuleRestrictionComparison

/-! The original AS condition gives finite-dimensional genuine Tor of
the semisimple right quotient against every finite-dimensional left
module, in every homological degree. In particular this applies to the
actual radical quotient on the left. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem ASRegular.cutSemisimpleRightTor_finite
    (hAS : A.ASRegular Q) (N : ModuleCat.{v} (hAS.CutGradedAlgebra A Q))
    [Module.Finite k N] (n : ℕ) :
    Module.Finite k ((balancedTensorTorLeftFunctor.{u,v,v,v} k
      (hAS.CutGradedAlgebra A Q) N n).obj (hAS.cutSemisimpleRightObject A Q)) := by
  letI := hAS.cutSemisimpleRightProjectiveResolution_finite A Q n
  exact balancedTensorTorLeft_finite_of_resolution_term k (hAS.CutGradedAlgebra A Q)
    N (hAS.cutSemisimpleRightObject A Q)
    (hAS.cutSemisimpleRightProjectiveResolution A Q) n

noncomputable def ASRegular.cutSemisimpleLeftObject (hAS : A.ASRegular Q) :
    ModuleCat.{v} (hAS.CutGradedAlgebra A Q) :=
  ModuleCat.of _ (hAS.CutGradedAlgebra A Q ⧸ hAS.cutGradedRadical A Q)

theorem ASRegular.cutSemisimpleLeftObject_finite (hAS : A.ASRegular Q) :
    Module.Finite k (hAS.cutSemisimpleLeftObject A Q) := by
  haveI : Module.Finite k (hAS.CutGradedAlgebra A Q ⧸ hAS.cutGradedRadical A Q) :=
    Module.Finite.equiv (hAS.cutGradedRadicalQuotientAlgEquiv A Q).symm.toLinearEquiv
  exact Module.Finite.equiv
    (algebraModuleRestrictScalarsIso k (hAS.CutGradedAlgebra A Q)
      (hAS.CutGradedAlgebra A Q ⧸ hAS.cutGradedRadical A Q)).toLinearEquiv.symm

theorem ASRegular.cutSemisimpleTor_finite (hAS : A.ASRegular Q) (n : ℕ) :
    Module.Finite k ((balancedTensorTorLeftFunctor.{u,v,v,v} k
      (hAS.CutGradedAlgebra A Q) (hAS.cutSemisimpleLeftObject A Q) n).obj
        (hAS.cutSemisimpleRightObject A Q)) := by
  letI := hAS.cutSemisimpleLeftObject_finite A Q
  exact hAS.cutSemisimpleRightTor_finite A Q (hAS.cutSemisimpleLeftObject A Q) n

end ASGinzburg.ZAlgebra
