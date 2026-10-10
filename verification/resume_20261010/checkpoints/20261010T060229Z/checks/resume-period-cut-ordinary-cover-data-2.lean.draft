import work.ASGinzburgDraft.PeriodCutOrdinaryGradedNakayama
import ASGinzburg.PeriodCutGradedBoundedMinimalResolution
import ASGinzburg.PeriodCutGradedForgetPreservation
import ASGinzburg.GradedOrdinaryProjectiveCover
import ASGinzburg.RightTopBasisKernelMinimality
import ASGinzburg.AlgebraModuleRestrictionComparison

/-! The native integer grading remains a genuine internal grading after
passing to the ordinary right-module category. A sharp height bound keeps
the original lower bound in the native top-basis projective cover. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices : ℤ))

theorem cutRecoveredRightModule_isZero_above_sharp_lower_bound
    (N : E.CutGradedRightModule Q) (b : ℤ)
    (hb : ∀ q : ℤ, q < b → N.grade q = ⊥)
    (i : ℤ) (hi : (Q.vertices : ℤ) * (-b) + (Q.vertices : ℤ) - 1 < i) :
    IsZero (((E.cornerCoverZAlgebra Q).rightModuleEvaluation i).obj N.recoveredRightModule) := by
  let z := Q.heightEquiv.symm i
  have hzheight : (z.1.val : ℤ) + (Q.vertices : ℤ) * z.2 = i := by
    have h := Q.heightEquiv.apply_symm_apply i
    rw [Q.heightEquiv_apply] at h
    exact h
  have hv : (z.1.val : ℤ) < (Q.vertices : ℤ) := by exact_mod_cast z.1.isLt
  have hzq : -z.2 < b := by
    by_contra h
    have hs : z.2 ≤ -b := by omega
    have hmul := mul_le_mul_of_nonneg_left hs
      (show (0 : ℤ) ≤ (Q.vertices : ℤ) by positivity)
    omega
  have hgrade := hb (-z.2) hzq
  have hzero : ∀ x : N.componentSubmodule z, x.val = 0 := by
    intro x
    have hx := ((N.mem_componentSubmodule_iff z x.val).mp x.property).1
    rw [hgrade] at hx
    simpa only [Submodule.mem_bot] using hx
  apply ModuleCat.isZero_iff_subsingleton.mpr
  change Subsingleton ↥(N.componentSubmodule z)
  exact ⟨fun x y => Subtype.ext ((hzero x).trans (hzero y).symm)⟩

theorem cutCornerModule_grade_eq_bot_of_sharp_height_bound
    (N : (E.cornerCoverZAlgebra Q).RightModule) (b : ℤ)
    (hb : ∀ i : ℤ, (Q.vertices : ℤ) * (-b) + (Q.vertices : ℤ) - 1 < i →
      IsZero (((E.cornerCoverZAlgebra Q).rightModuleEvaluation i).obj N))
    (q : ℤ) (hq : q < b) : (E.cornerGradedRightModule Q N).grade q = ⊥ := by
  have hheight (i : Q.Vertex) :
      (Q.vertices : ℤ) * (-b) + (Q.vertices : ℤ) - 1 < Q.heightEquiv (i, -q) := by
    rw [Q.heightEquiv_apply]
    change (Q.vertices : ℤ) * (-b) + (Q.vertices : ℤ) - 1 <
      (i.val : ℤ) + (Q.vertices : ℤ) * -q
    have hi : 0 ≤ (i.val : ℤ) := Nat.cast_nonneg _
    have hn : 0 ≤ (Q.vertices : ℤ) := Nat.cast_nonneg _
    have hmul := mul_le_mul_of_nonneg_left (show -b + 1 ≤ -q by omega) hn
    nlinarith
  letI : ∀ i : Q.Vertex, Subsingleton (E.CornerModuleSpace Q N (i, -q)) := fun i =>
    ModuleCat.isZero_iff_subsingleton.mp (hb (Q.heightEquiv (i, -q)) (hheight i))
  letI : Subsingleton (E.CornerModuleDegreeSpace Q N q) := inferInstance
  change E.cornerModuleGrade Q N q = ⊥
  apply le_antisymm _ bot_le
  rintro v ⟨w, rfl⟩
  have hw : w = 0 := Subsingleton.elim _ _
  rw [hw, map_zero]
  exact Submodule.zero_mem _

end ASGinzburg.ZAlgebra.PeriodIso
