import work.ASGinzburgDraft.ASCutOrdinaryRegularTopHomFieldEquiv
import work.ASGinzburgDraft.OrdinaryRingDualTopExtIso
import ASGinzburg.OrdinaryModuleRingDual

/-! The original AS condition identifies actual ordinary Ext-three
from a native vertex simple to the right regular module with the field. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u v
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 200000
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)
attribute [local instance 2000] ordinaryRingDualExtStandardDerivedCategory
attribute [local instance 2500] ModuleCat.linearOverField
attribute [local instance] exactExtModule

noncomputable def ASRegular.cutOrdinarySimpleExt_regular_three_fieldEquiv
    (hAS : A.ASRegular Q) (i : Q.Vertex) :
    Abelian.Ext.{v} (hAS.cutOrdinarySimple A Q (i,0))
      (ModuleCat.of (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ) 3 ≃ₗ[k] k := by
  let R := (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ
  let P := hAS.cutForgottenGradedSimpleProjectiveResolution A Q i
  let h₄ := hAS.cutForgottenGradedSimpleResolution_isZero_ge_four A Q i 0
  let e₁ : ordinaryRingDualTopQuotient k R (P.complex.d 3 2) ≃ₗ[k]
      Abelian.Ext.{v} (hAS.cutOrdinarySimple A Q (i,0)) (ModuleCat.of R R) 3 :=
    ordinaryRingDualTopActualExtThreeLinearEquiv k R P h₄
  let e₂ : ordinaryRingDualTopQuotient k R (P.complex.d 3 2) ≃ₗ[k] k :=
    hAS.cutOrdinarySimpleRingDual_topQuotientFieldEquiv A Q i
  exact e₁.symm.trans e₂

noncomputable def ASRegular.cutOrdinarySimpleExt_rightRegular_three_fieldEquiv
    (hAS : A.ASRegular Q) (i : Q.Vertex) :
    Abelian.Ext.{v} (hAS.cutOrdinarySimple A Q (i,0))
      (ModuleCat.of (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ (hAS.CutGradedAlgebra A Q)) 3 ≃ₗ[k] k := by
  let iso := (rightRegularOppositeLinearEquiv (hAS.CutGradedAlgebra A Q)).toModuleIso
  let e₁ := exactExtPostcompIso k (M := hAS.cutOrdinarySimple A Q (i,0)) iso 3
  let e₂ := hAS.cutOrdinarySimpleExt_regular_three_fieldEquiv A Q i
  exact e₁.trans e₂

end ASGinzburg.ZAlgebra
