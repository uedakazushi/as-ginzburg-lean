import ASGinzburg.PeriodCutRecoveredTotalRActions
import ASGinzburg.PeriodCutGradedModuleRadical

/-! The genuine recovered total-space equivalence identifies the actual
graded radical action spans in both directions. -/
namespace ASGinzburg.ZAlgebra.PeriodIso.CutGradedRightModule
open CategoryTheory
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable {Q : CutQuiver} {E : A.PeriodIso (Q.vertices:ℤ)}

theorem recoveredTotalEquiv_symm_mem_radical
    (M : E.CutGradedRightModule Q) {v : M.space}
    (hv : v ∈ M.gradedRadicalActionSpan) :
    M.recoveredTotalEquiv.symm v ∈
      (E.cornerGradedRightModule Q M.recoveredRightModule).gradedRadicalActionSpan := by
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨r, hr, x, rfl⟩ := hy
    rw [M.recoveredTotalEquiv_symm_representation_action]
    exact (E.cornerGradedRightModule Q M.recoveredRightModule).gradedRadicalAction_mem
      r hr (M.recoveredTotalEquiv.symm x)
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
    rw [map_add]
    exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih =>
    rw [map_smul]
    exact Submodule.smul_mem _ c ih

theorem recoveredTotalEquiv_mem_radical
    (M : E.CutGradedRightModule Q)
    {v : E.CornerModuleTotalSpace Q M.recoveredRightModule}
    (hv : v ∈ (E.cornerGradedRightModule Q M.recoveredRightModule).gradedRadicalActionSpan) :
    M.recoveredTotalEquiv v ∈ M.gradedRadicalActionSpan := by
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨r, hr, x, rfl⟩ := hy
    have he := LinearMap.congr_fun (M.recoveredTotalEquiv_representation_action r) x
    change M.recoveredTotalEquiv ((E.cutRightRepresentation Q M.recoveredRightModule r).unop x) =
      (M.representation r).unop (M.recoveredTotalEquiv x) at he
    change M.recoveredTotalEquiv ((E.cutRightRepresentation Q M.recoveredRightModule r).unop x) ∈ _
    rw [he]
    exact M.gradedRadicalAction_mem r hr (M.recoveredTotalEquiv x)
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
    rw [map_add]
    exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih =>
    rw [map_smul]
    exact Submodule.smul_mem _ c ih

theorem recoveredTotalEquiv_mem_radical_iff
    (M : E.CutGradedRightModule Q)
    (v : E.CornerModuleTotalSpace Q M.recoveredRightModule) :
    M.recoveredTotalEquiv v ∈ M.gradedRadicalActionSpan ↔
      v ∈ (E.cornerGradedRightModule Q M.recoveredRightModule).gradedRadicalActionSpan := by
  constructor
  · intro hv
    simpa only [LinearEquiv.symm_apply_apply] using M.recoveredTotalEquiv_symm_mem_radical hv
  · exact M.recoveredTotalEquiv_mem_radical

end ASGinzburg.ZAlgebra.PeriodIso.CutGradedRightModule
