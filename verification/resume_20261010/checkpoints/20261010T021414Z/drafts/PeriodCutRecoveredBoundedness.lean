import ASGinzburg.PeriodCutRecoveredRightModules
import ASGinzburg.RightModuleAbelian

/-! An actual lower bound for the internal integer grading supplies
an explicit upper height bound for the recovered directed-cover module. -/
namespace ASGinzburg.ZAlgebra.PeriodIso.CutGradedRightModule
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable {Q : CutQuiver} {E : A.PeriodIso (Q.vertices:ℤ)}

theorem recoveredRightModule_isZero_above_of_grade_lower_bound
    (M : E.CutGradedRightModule Q) (b : ℤ)
    (hb : ∀ q : ℤ, q < b → M.grade q = ⊥)
    (i : ℤ) (hi : (Q.vertices:ℤ)*(-b)+(Q.vertices:ℤ) < i) :
    IsZero (((E.cornerCoverZAlgebra Q).rightModuleEvaluation i).obj M.recoveredRightModule) := by
  let z := Q.heightEquiv.symm i
  have hzheight : (z.1.val:ℤ)+(Q.vertices:ℤ)*z.2 = i := by
    have h := Q.heightEquiv.apply_symm_apply i
    rw [Q.heightEquiv_apply] at h
    exact h
  have hv : (z.1.val:ℤ) < (Q.vertices:ℤ) := by
    exact_mod_cast z.1.isLt
  have hzq : -z.2 < b := by
    by_contra h
    have hs : z.2 ≤ -b := by omega
    have hmul := mul_le_mul_of_nonneg_left hs
      (show (0:ℤ) ≤ (Q.vertices:ℤ) by positivity)
    omega
  have hgrade := hb (-z.2) hzq
  have hzero : ∀ x : M.componentSubmodule z, x.val = 0 := by
    intro x
    have hx := ((M.mem_componentSubmodule_iff z x.val).mp x.property).1
    rw [hgrade] at hx
    exact Submodule.mem_bot.mp hx
  apply ModuleCat.isZero_iff_subsingleton.mpr
  change Subsingleton ↥(M.componentSubmodule z)
  exact ⟨fun x y => Subtype.ext ((hzero x).trans (hzero y).symm)⟩

end ASGinzburg.ZAlgebra.PeriodIso.CutGradedRightModule
