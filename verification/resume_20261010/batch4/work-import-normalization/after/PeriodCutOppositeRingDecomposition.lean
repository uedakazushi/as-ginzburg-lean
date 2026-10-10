import ASGinzburg.PeriodCutOrdinaryGradedNakayama
import work.ASGinzburgDraft.HomogeneousLinearEquivImageGrading
import work.ASGinzburgDraft.GradedOrdinaryProjectiveLift
import ASGinzburg.PeriodCutRegularGrading

/-! The actual native opposite ring grading is internal, and genuinely
graded ordinary projective modules admit homogeneous epimorphism lifts. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory
open scoped ModuleCat.Algebra DirectSum
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))
local notation "R" => E.CutGradedRing (fun i : Q.Vertex => (Fin.val i:ℤ))

noncomputable def cutIntegerOppositeGradeDecomposition :
    DirectSum.Decomposition (E.cutIntegerOppositeHomogeneousSpace Q) := by
  letI := E.cutIntegerRegularGradeDecomposition Q
  exact homogeneousLinearEquivImageDecomposition (MulOpposite.opLinearEquiv k)
    (E.cutIntegerHomogeneousSpace Q)

theorem cutOrdinaryGradedProjectiveLift
    (P M N : GradedOrdinaryModuleData k Rᵐᵒᵖ (E.cutIntegerOppositeHomogeneousSpace Q))
    (q : P.ringModule ⟶ N.ringModule) (π : M.ringModule ⟶ N.ringModule)
    (hq : P.PreservesGrade N q) (hπ : M.PreservesGrade N π)
    [Projective P.ringModule] [Epi π] :
    ∃ f : P.ringModule ⟶ M.ringModule, P.PreservesGrade M f ∧ f ≫ π = q := by
  letI := E.cutIntegerOppositeGradeDecomposition Q
  exact P.exists_gradePreserving_projective_lift M N q π hq hπ

end ASGinzburg.ZAlgebra.PeriodIso
