import work.ASGinzburgDraft.ASCutSemisimpleRegularTopExtFieldEquiv

/-! Coordinates of the actual semisimple Ext-three equivalence use
precomposition by the actual native simple inclusions. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u v
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 200000
attribute [local instance 2000] ordinaryRingDualExtStandardDerivedCategory
attribute [local instance 2500] ModuleCat.linearOverField
attribute [local instance] exactExtModule
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem ASRegular.cutSemisimpleRightExt_rightRegular_three_vertexFieldEquiv_apply
    (hAS : A.ASRegular Q)
    (e : Abelian.Ext.{v} (hAS.cutSemisimpleRightObject A Q)
      (ModuleCat.of (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ (hAS.CutGradedAlgebra A Q)) 3)
    (i : Q.Vertex) :
    hAS.cutSemisimpleRightExt_rightRegular_three_vertexFieldEquiv A Q e i =
      hAS.cutOrdinarySimpleExt_rightRegular_three_fieldEquiv A Q i
        ((Abelian.Ext.mk₀
          (biproduct.ι (fun j : Q.Vertex => hAS.cutOrdinarySimple A Q (j,0)) i ≫
            (hAS.cutSemisimpleRightVertexIso A Q).inv)).comp e (zero_add 3)) := by
  change hAS.cutOrdinarySimpleExt_rightRegular_three_fieldEquiv A Q i
      ((Abelian.Ext.mk₀
        (biproduct.ι (fun j : Q.Vertex => hAS.cutOrdinarySimple A Q (j,0)) i)).comp
        ((Abelian.Ext.mk₀ (hAS.cutSemisimpleRightVertexIso A Q).inv).comp e
          (zero_add 3)) (zero_add 3)) = _
  rw [Abelian.Ext.mk₀_comp_mk₀_assoc]

end ASGinzburg.ZAlgebra
