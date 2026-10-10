import ASGinzburg.PeriodCutRecoveredTotalComparison
import ASGinzburg.RightModuleAbelian

/-! The concrete recovery construction detects the actual zero vector
space of a graded module, using its proved total-space equivalence. -/
namespace ASGinzburg.ZAlgebra.PeriodIso.CutGradedRightModule
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable {Q : CutQuiver} {E : A.PeriodIso (Q.vertices:ℤ)}

theorem recoveredRightModule_isZero_iff_subsingleton_space
    (M : E.CutGradedRightModule Q) :
    IsZero M.recoveredRightModule ↔ Subsingleton M.space := by
  constructor
  · intro hM
    letI : ∀ x : Q.LiftVertex,
        Subsingleton (E.CornerModuleSpace Q M.recoveredRightModule x) := fun x =>
      ModuleCat.isZero_iff_subsingleton.mp
        (((E.cornerCoverZAlgebra Q).rightModuleEvaluation (Q.heightEquiv x)).map_isZero hM)
    letI : Subsingleton (E.CornerModuleTotalSpace Q M.recoveredRightModule) := inferInstance
    exact ⟨fun a b => M.recoveredTotalEquiv.symm.injective (Subsingleton.elim _ _)⟩
  · intro hM
    letI := hM
    apply (IsZero.iff_id_eq_zero M.recoveredRightModule).mpr
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Subsingleton.elim _ _

end ASGinzburg.ZAlgebra.PeriodIso.CutGradedRightModule
