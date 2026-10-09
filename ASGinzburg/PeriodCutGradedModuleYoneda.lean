import ASGinzburg.PeriodCutGradedModuleAbelian
import ASGinzburg.LinearEquivalenceAdjunction

/-! A concrete graded R-projective represents its vertex-degree component. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

noncomputable def cornerGradedRepresentable (z : Q.LiftVertex) : E.CutGradedRightModule Q :=
  E.cornerGradedRightModule Q ((E.cornerCoverZAlgebra Q).representable (Q.heightEquiv z))

noncomputable def cornerGradedRepresentableYonedaEquiv (z : Q.LiftVertex)
    (M : E.CutGradedRightModule Q) :
    (E.cornerGradedRepresentable Q z ⟶ M) ≃ₗ[k] M.componentSubmodule z :=
  ((ASGinzburg.equivalenceAdjunctionHomLinearEquiv (E.cornerGradedModuleEquivalence Q)
    ((E.cornerCoverZAlgebra Q).representable (Q.heightEquiv z)) M).trans
      ((E.cornerCoverZAlgebra Q).representableYonedaEquiv (Q.heightEquiv z) M.recoveredRightModule)).trans
        (M.recoveredCoordinateSpaceEquiv z)

end ASGinzburg.ZAlgebra.PeriodIso
