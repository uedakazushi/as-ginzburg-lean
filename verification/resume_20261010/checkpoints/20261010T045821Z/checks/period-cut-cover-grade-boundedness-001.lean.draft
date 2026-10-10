import ASGinzburg.PeriodCutGradedRightModules
import ASGinzburg.RightModuleHomology

/-! An upper bound on the actual cover's height support gives a lower bound
on the native module's integer grading, whose degree is minus the sheet. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory Limits
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices : ℤ))

theorem cornerCoverHeight_above_bound_of_degree_below
    (b q : ℤ) (hq : q < -(Int.natAbs b : ℤ)) (i : Q.Vertex) :
    b < Q.heightEquiv (i, -q) := by
  rw [Q.heightEquiv_apply]
  change b < (i.val : ℤ) + (Q.vertices : ℤ) * -q
  have hb : b ≤ (Int.natAbs b : ℤ) := Int.le_natAbs
  have hn : 1 ≤ (Q.vertices : ℤ) := by
    have := Q.at_least_three
    omega
  have hs : 0 ≤ -q := by omega
  have hm := mul_le_mul_of_nonneg_right hn hs
  have hi : 0 ≤ (i.val : ℤ) := Nat.cast_nonneg _
  nlinarith

theorem cornerModuleDegreeSpace_subsingleton_of_height_bound
    (M : (E.cornerCoverZAlgebra Q).RightModule) (b : ℤ)
    (hb : ∀ i : ℤ, b < i →
      IsZero (((E.cornerCoverZAlgebra Q).rightModuleEvaluation i).obj M))
    (q : ℤ) (hq : q < -(Int.natAbs b : ℤ)) :
    Subsingleton (E.CornerModuleDegreeSpace Q M q) := by
  letI : ∀ i : Q.Vertex, Subsingleton (E.CornerModuleSpace Q M (i, -q)) := fun i =>
    ModuleCat.isZero_iff_subsingleton.mp
      (hb (Q.heightEquiv (i, -q))
        (cornerCoverHeight_above_bound_of_degree_below Q b q hq i))
  infer_instance

theorem cornerGradedRightModule_grade_eq_bot_of_height_bound
    (M : (E.cornerCoverZAlgebra Q).RightModule) (b : ℤ)
    (hb : ∀ i : ℤ, b < i →
      IsZero (((E.cornerCoverZAlgebra Q).rightModuleEvaluation i).obj M))
    (q : ℤ) (hq : q < -(Int.natAbs b : ℤ)) :
    (E.cornerGradedRightModule Q M).grade q = ⊥ := by
  change E.cornerModuleGrade Q M q = ⊥
  letI := E.cornerModuleDegreeSpace_subsingleton_of_height_bound Q M b hb q hq
  apply le_antisymm _ bot_le
  rintro v ⟨w, rfl⟩
  have hw : w = 0 := Subsingleton.elim _ _
  rw [hw, map_zero]
  exact Submodule.zero_mem _

end ASGinzburg.ZAlgebra.PeriodIso
