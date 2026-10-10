import work.ASGinzburgDraft.ASCutEnvelopingRingHomRightTopProjectivity
import work.ASGinzburgDraft.ModuleCatCochainTopHomologyFunctorIso
import ASGinzburg.BalancedTensorLeftAdjunction

/-! True semisimple tensor reduction of actual degree-three enveloping
Ext is the top homology of the actual reduced native ring-dual complex. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 200000
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def ASRegular.cutEnvelopingRingDualExtThreeSemisimpleHomologyIso
    (hAS : A.ASRegular Q) :
    (balancedTensorLeftFunctor k (hAS.CutGradedAlgebra A Q)
      (hAS.CutGradedAlgebra A Q ⧸ hAS.cutGradedRadical A Q)).obj
        ((envelopingOppositeLeftRestrictionFunctor k (hAS.CutGradedAlgebra A Q)).obj
          (hAS.cutEnvelopingRingDualExtObject A Q 3)) ≅
      (((balancedTensorLeftFunctor k (hAS.CutGradedAlgebra A Q)
        (hAS.CutGradedAlgebra A Q ⧸ hAS.cutGradedRadical A Q)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          (hAS.cutEnvelopingMinimalRingHomRightNatComplex A Q)).homology 3 := by
  let K := hAS.cutEnvelopingMinimalRingHomRightNatComplex A Q
  let F := balancedTensorLeftFunctor k (hAS.CutGradedAlgebra A Q)
    (hAS.CutGradedAlgebra A Q ⧸ hAS.cutGradedRadical A Q)
  exact F.mapIso (hAS.cutEnvelopingRingDualExtRightHomologyIso A Q 3) ≪≫
    moduleCatCochainHomologyThreeFunctorIso K F
      (hAS.cutEnvelopingMinimalRingHomRightNatComplex_isZero_ge_four A Q 0)

end ASGinzburg.ZAlgebra
