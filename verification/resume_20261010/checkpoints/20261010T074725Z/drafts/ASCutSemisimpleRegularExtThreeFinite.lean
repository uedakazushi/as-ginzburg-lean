import work.ASGinzburgDraft.FiniteBiproductLinearExt
import work.ASGinzburgDraft.ASCutOrdinaryRegularExtThreeFinite
import ASGinzburg.ASCutSemisimpleRightDimension

/-! The original AS condition makes actual ordinary Ext-three from the
actual right semisimple quotient finite over the field. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u v
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
attribute [local instance 2000] ordinaryRingDualExtStandardDerivedCategory
attribute [local instance 2500] ModuleCat.linearOverField
attribute [local instance] exactExtModule
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem ASRegular.cutSemisimpleRightExt_rightRegular_three_finite (hAS : A.ASRegular Q) :
    Module.Finite k (Abelian.Ext.{v} (hAS.cutSemisimpleRightObject A Q)
      (ModuleCat.of (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ (hAS.CutGradedAlgebra A Q)) 3) := by
  let R := hAS.CutGradedAlgebra A Q
  let Y := ModuleCat.of Rᵐᵒᵖ R
  let e := hAS.cutSemisimpleRightVertexIso A Q
  apply exactExt_finite_of_sourceIso k e 3
  apply exactExtFiniteBiproduct_finite k
    (biproduct.isBilimit (fun i : Q.Vertex => hAS.cutOrdinarySimple A Q (i,0))) Y 3
  intro i
  exact hAS.cutOrdinarySimpleExt_rightRegular_three_finite A Q i

end ASGinzburg.ZAlgebra
