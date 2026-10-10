import work.ASGinzburgDraft.ASCutOrdinaryRegularHomogeneousTopQuotientEquiv
import work.ASGinzburgDraft.PeriodCutOrdinaryRingDualTopHomQuotient
import work.ASGinzburgDraft.ASCutGradedRegularTopHomQuotientFieldEquiv

/-! The actual whole ordinary top dual cokernel of the native AS simple
resolution is one copy of the field, through its genuine homogeneous
minus-one cokernel and the actual graded final Hom cokernel. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
open scoped ModuleCat.Algebra
attribute [local instance 4000] ordinaryRingDualUnbundledAddCommGroup
attribute [local instance 4000] PeriodIso.cutOrdinaryRingDualTopHomAddCommGroup
attribute [local instance 4000] PeriodIso.cutOrdinaryRingDualTopHomFieldModule
attribute [local instance 3000] GradedOrdinaryModuleData.ringDualGradeHasQuotient
universe u v
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 200000
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def ASRegular.cutOrdinarySimpleRingDual_topShiftedHomQuotientEquiv
    (hAS : A.ASRegular Q) (i : Q.Vertex) :
    ordinaryRingDualTopQuotient k (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ
      ((hAS.cutForgottenGradedSimpleProjectiveResolution A Q i).complex.d 3 2) ≃ₗ[k]
      (((hAS.cutGradedSimpleProjectiveResolution A Q (i,0)).complex.X 3 ⟶
        (((hAS.periodIso A Q).cutRegularGradedRightModule Q).shifted (-1))) ⧸
      LinearMap.range (Linear.leftComp k
        (((hAS.periodIso A Q).cutRegularGradedRightModule Q).shifted (-1))
        ((hAS.cutGradedSimpleProjectiveResolution A Q (i,0)).complex.d 3 2))) := by
  let E := hAS.periodIso A Q
  let R := (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ
  let G := hAS.cutGradedSimpleProjectiveResolution A Q (i,0)
  let P := hAS.cutForgottenGradedSimpleProjectiveResolution A Q i
  let M := hAS.cutOrdinarySimpleResolutionTermData A Q i 3
  let L := hAS.cutOrdinarySimpleResolutionTermData A Q i 2
  let N := (E.cutRegularGradedRightModule Q).shifted (-1)
  letI := E.cutIntegerOppositeGradeDecomposition Q
  let e₁ : M.ringDualHomogeneousTopQuotient L (P.complex.d 3 2)
      (hAS.cutForgottenGradedSimpleResolution_d_preservesGrade A Q i 2) (-1) ≃ₗ[k]
      ordinaryRingDualTopQuotient k R (P.complex.d 3 2) :=
    hAS.cutOrdinarySimpleRingDual_homogeneousTopQuotientEquiv A Q i
  let e₂ : M.ringDualHomogeneousTopQuotient L (P.complex.d 3 2)
      (hAS.cutForgottenGradedSimpleResolution_d_preservesGrade A Q i 2) (-1) ≃ₗ[k]
      ((G.complex.X 3 ⟶ N) ⧸
        LinearMap.range (Linear.leftComp k N (G.complex.d 3 2))) :=
    E.cutOrdinaryRingDualTopShiftedHomQuotientEquiv Q (G.complex.d 3 2) (-1)
  exact e₁.symm.trans e₂

noncomputable def ASRegular.cutOrdinarySimpleRingDual_topQuotientFieldEquiv
    (hAS : A.ASRegular Q) (i : Q.Vertex) :
    ordinaryRingDualTopQuotient k (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ
      ((hAS.cutForgottenGradedSimpleProjectiveResolution A Q i).complex.d 3 2) ≃ₗ[k] k :=
  (hAS.cutOrdinarySimpleRingDual_topShiftedHomQuotientEquiv A Q i).trans
    (hAS.cutGradedRegularTopHomQuotientFieldEquiv A Q i)

end ASGinzburg.ZAlgebra
