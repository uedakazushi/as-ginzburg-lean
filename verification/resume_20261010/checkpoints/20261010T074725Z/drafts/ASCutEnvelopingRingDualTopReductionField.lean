import work.ASGinzburgDraft.ASCutEnvelopingRingDualTopReduction
import work.ASGinzburgDraft.ASCutEnvelopingReducedRingHomComplexIso
import work.ASGinzburgDraft.OrdinaryRightRingHomFieldTopExtIso
import work.ASGinzburgDraft.ASCutSemisimpleRegularTopExtFieldEquiv

/-! The actual semisimple tensor reduction of original-AS enveloping
Ext-three has one field coordinate for each native vertex. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u v
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 200000
attribute [local instance 2000] ordinaryRingDualExtStandardDerivedCategory
attribute [local instance 2500] ModuleCat.linearOverField
attribute [local instance] exactExtModule
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def ASRegular.cutEnvelopingRingDualExtThreeSemisimpleVertexFieldEquiv
    (hAS : A.ASRegular Q) :
    ((balancedTensorLeftFunctor k (hAS.CutGradedAlgebra A Q)
      (hAS.CutGradedAlgebra A Q ⧸ hAS.cutGradedRadical A Q)).obj
        ((envelopingOppositeLeftRestrictionFunctor k (hAS.CutGradedAlgebra A Q)).obj
          (hAS.cutEnvelopingRingDualExtObject A Q 3))) ≃ₗ[k] (Q.Vertex → k) := by
  let R := hAS.CutGradedAlgebra A Q
  let F := balancedTensorLeftFunctor k R (R ⧸ hAS.cutGradedRadical A Q)
  let U := moduleCatULiftFunctor.{u,v,u} k
  let W := F.obj ((envelopingOppositeLeftRestrictionFunctor k R).obj
    (hAS.cutEnvelopingRingDualExtObject A Q 3))
  let K := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (hAS.cutEnvelopingMinimalRingHomRightNatComplex A Q)
  let P := envelopingBalancedTensorRegularProjectiveResolution k R
    (hAS.cutSemisimpleRightObject A Q) (hAS.cutEnvelopingRegularMinimalResolution A Q)
  let i₁ : U.obj W ≅ U.obj (K.homology 3) :=
    U.mapIso (hAS.cutEnvelopingRingDualExtThreeSemisimpleHomologyIso A Q)
  let i₂ : U.obj (K.homology 3) ≅
      ((U.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology 3 :=
    ((K.sc 3).mapHomologyIso U).symm
  let i₃ := (HomologicalComplex.homologyFunctor (ModuleCat.{max u v} k)
    (ComplexShape.up ℕ) 3).mapIso
      (hAS.cutEnvelopingMinimalReducedRingHomOrdinaryFieldComplexIso A Q)
  let i₄ := ordinaryRightRingHomFieldHomologyThreeExtIso k R P
    (envelopingBalancedTensorRegularProjectiveResolution_term_four_isZero k R
      (hAS.cutSemisimpleRightObject A Q) (hAS.cutEnvelopingRegularMinimalResolution A Q)
      (hAS.cutEnvelopingRegularMinimalResolution_isZero_ge_four A Q 0))
  let e : ULift.{u} W ≃ₗ[k]
      ULift.{u} (Abelian.Ext.{v} (hAS.cutSemisimpleRightObject A Q)
        (ModuleCat.of Rᵐᵒᵖ R) 3) := (i₁ ≪≫ i₂ ≪≫ i₃ ≪≫ i₄).toLinearEquiv
  exact ((ULift.moduleEquiv.symm.trans e).trans ULift.moduleEquiv).trans
    (hAS.cutSemisimpleRightExt_rightRegular_three_vertexFieldEquiv A Q)

theorem ASRegular.cutEnvelopingRingDualExtThreeSemisimple_finrank
    (hAS : A.ASRegular Q) :
    Module.finrank k ((balancedTensorLeftFunctor k (hAS.CutGradedAlgebra A Q)
      (hAS.CutGradedAlgebra A Q ⧸ hAS.cutGradedRadical A Q)).obj
        ((envelopingOppositeLeftRestrictionFunctor k (hAS.CutGradedAlgebra A Q)).obj
          (hAS.cutEnvelopingRingDualExtObject A Q 3))) = Q.vertices := by
  rw [(hAS.cutEnvelopingRingDualExtThreeSemisimpleVertexFieldEquiv A Q).finrank_eq]
  simp [CutQuiver.Vertex]

end ASGinzburg.ZAlgebra
