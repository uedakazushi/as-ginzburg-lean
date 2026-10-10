import work.ASGinzburgDraft.FiniteBiproductLinearExt
import work.ASGinzburgDraft.ASCutOrdinaryRegularTopExtFieldEquiv
import ASGinzburg.ASCutSemisimpleRightDimension
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The original AS condition identifies the actual right semisimple
ordinary Ext-three with one copy of the field for each native vertex. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u v
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 200000
attribute [local instance 2000] ordinaryRingDualExtStandardDerivedCategory
attribute [local instance 2500] ModuleCat.linearOverField
attribute [local instance] exactExtModule
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def ASRegular.cutSemisimpleRightExt_rightRegular_three_vertexFieldEquiv
    (hAS : A.ASRegular Q) :
    Abelian.Ext.{v} (hAS.cutSemisimpleRightObject A Q)
      (ModuleCat.of (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ (hAS.CutGradedAlgebra A Q)) 3 ≃ₗ[k]
      (Q.Vertex → k) := by
  let R := hAS.CutGradedAlgebra A Q
  let Y := ModuleCat.of Rᵐᵒᵖ R
  let X : Q.Vertex → ModuleCat.{v} Rᵐᵒᵖ := fun i => hAS.cutOrdinarySimple A Q (i,0)
  let e₁ : Abelian.Ext.{v} (hAS.cutSemisimpleRightObject A Q) Y 3 ≃ₗ[k]
      Abelian.Ext.{v} (⨁ X) Y 3 :=
    (exactExtSourceIsoLinearEquiv k (Y := Y)
      (hAS.cutSemisimpleRightVertexIso A Q) 3).symm
  let e₂ : Abelian.Ext.{v} (⨁ X) Y 3 ≃ₗ[k]
      (∀ i : Q.Vertex, Abelian.Ext.{v} (X i) Y 3) :=
    exactExtFiniteBiproductLinearEquiv k (biproduct.isBilimit X) Y 3
  let e₃ : (∀ i : Q.Vertex, Abelian.Ext.{v} (X i) Y 3) ≃ₗ[k] (Q.Vertex → k) :=
    LinearEquiv.piCongrRight (fun i =>
      hAS.cutOrdinarySimpleExt_rightRegular_three_fieldEquiv A Q i)
  exact (e₁.trans e₂).trans e₃

theorem ASRegular.cutSemisimpleRightExt_rightRegular_three_finrank
    (hAS : A.ASRegular Q) :
    Module.finrank k (Abelian.Ext.{v} (hAS.cutSemisimpleRightObject A Q)
      (ModuleCat.of (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ (hAS.CutGradedAlgebra A Q)) 3) = Q.vertices := by
  rw [(hAS.cutSemisimpleRightExt_rightRegular_three_vertexFieldEquiv A Q).finrank_eq]
  simp [CutQuiver.Vertex]

end ASGinzburg.ZAlgebra
