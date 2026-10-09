import ASGinzburg.PeriodCutRecoveredTotalRActions
import ASGinzburg.PeriodCutRecoveredInverseGrading
import ASGinzburg.PeriodCutGradedModuleCategory

/-! Recovering a cover module from a graded R module and taking its
actual graded R module returns an isomorphic graded R module. -/
namespace ASGinzburg.ZAlgebra.PeriodIso.CutGradedRightModule
open CategoryTheory
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable {Q : CutQuiver} {E : A.PeriodIso (Q.vertices:ℤ)}

noncomputable def recoveredGradedModuleIso (M : E.CutGradedRightModule Q) :
    E.cornerGradedRightModule Q M.recoveredRightModule ≅ M where
  hom := ⟨M.recoveredTotalEquiv.toLinearMap,⟨
    fun r x => LinearMap.congr_fun (M.recoveredTotalEquiv_representation_action r) x,
    M.recoveredTotalEquiv_mem_grade⟩⟩
  inv := ⟨M.recoveredTotalEquiv.symm.toLinearMap,⟨
    M.recoveredTotalEquiv_symm_representation_action,M.recoveredTotalEquiv_symm_mem_grade⟩⟩
  hom_inv_id := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    exact M.recoveredTotalEquiv.symm_apply_apply x
  inv_hom_id := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    exact M.recoveredTotalEquiv.apply_symm_apply x

end ASGinzburg.ZAlgebra.PeriodIso.CutGradedRightModule
