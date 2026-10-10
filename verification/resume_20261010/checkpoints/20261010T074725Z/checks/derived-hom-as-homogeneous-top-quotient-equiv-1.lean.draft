import work.ASGinzburgDraft.GradedOrdinaryRingDualHomogeneousTopQuotient
import work.ASGinzburgDraft.ASCutOrdinaryRegularTopQuotientFinite

/-! Original AS regularity identifies the actual whole ordinary top
cokernel with its genuine internal degree minus-one cokernel. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
open scoped ModuleCat.Algebra
attribute [local instance 4000] ordinaryRingDualUnbundledAddCommGroup
universe u v
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 200000
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def ASRegular.cutOrdinarySimpleRingDual_homogeneousTopQuotientEquiv
    (hAS : A.ASRegular Q) (i : Q.Vertex) :
    letI := (hAS.periodIso A Q).cutIntegerOppositeGradeDecomposition Q
    (hAS.cutOrdinarySimpleResolutionTermData A Q i 3).ringDualHomogeneousTopQuotient
      (hAS.cutOrdinarySimpleResolutionTermData A Q i 2)
      ((hAS.cutForgottenGradedSimpleProjectiveResolution A Q i).complex.d 3 2)
      (hAS.cutForgottenGradedSimpleResolution_d_preservesGrade A Q i 2) (-1) ≃ₗ[k]
        ordinaryRingDualTopQuotient k (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ
          ((hAS.cutForgottenGradedSimpleProjectiveResolution A Q i).complex.d 3 2) := by
  let E := hAS.periodIso A Q
  let R := (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ
  let P := hAS.cutForgottenGradedSimpleProjectiveResolution A Q i
  let M := hAS.cutOrdinarySimpleResolutionTermData A Q i 3
  let L := hAS.cutOrdinarySimpleResolutionTermData A Q i 2
  letI := E.cutIntegerOppositeGradeDecomposition Q
  letI : Module.Finite R M.ringModule :=
    hAS.cutOrdinarySimpleResolutionTermData_finite A Q i 3
  exact M.ringDualHomogeneousTopQuotientEquiv L
    (E.cutIntegerOppositeHomogeneousSpace_mul_mem Q) (P.complex.d 3 2)
    (hAS.cutForgottenGradedSimpleResolution_d_preservesGrade A Q i 2) (-1)
    (fun q hq f hf => hAS.cutOrdinarySimpleRingDual_top_boundary_other A Q i q hq f hf)

end ASGinzburg.ZAlgebra
