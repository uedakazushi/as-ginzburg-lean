import work.ASGinzburgDraft.RightBoundedMinimalResolution
import work.ASGinzburgDraft.PeriodCutRecoveredBoundedness
import work.ASGinzburgDraft.PeriodCutCoverGradeBoundedness
import work.ASGinzburgDraft.ProjectiveResolutionChangeTarget
import ASGinzburg.PeriodCutGradedMinimality
import ASGinzburg.PeriodCutGradedModuleAbelian

/-! Every actual bounded-below native graded right module has a genuine
minimal projective resolution, constructed from basis covers of its
recovered directed module. All terms retain a common grade lower bound.
This is a native cut result; it does not identify an enveloping algebra
with a native cut model. -/
namespace ASGinzburg.ZAlgebra.PeriodIso.CutGradedRightModule
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable {Q : CutQuiver} {E : A.PeriodIso (Q.vertices:ℤ)}

noncomputable def boundedBelowMinimalResolution
    (M : E.CutGradedRightModule Q) (b : ℤ)
    (hb : ∀ q : ℤ, q < b → M.grade q = ⊥) : ProjectiveResolution M :=
  projectiveResolutionChangeTarget
    (equivalenceProjectiveResolution (E.cornerGradedModuleEquivalence Q)
      ((E.cornerCoverZAlgebra Q).rightBoundedMinimalResolution M.recoveredRightModule
        ((Q.vertices:ℤ)*(-b)+(Q.vertices:ℤ))
        (M.recoveredRightModule_isZero_above_of_grade_lower_bound b hb)))
    M.recoveredGradedModuleIso

theorem boundedBelowMinimalResolution_grade_eq_bot
    (M : E.CutGradedRightModule Q) (b : ℤ)
    (hb : ∀ q : ℤ, q < b → M.grade q = ⊥)
    (n : ℕ) (q : ℤ)
    (hq : q < -(Int.natAbs ((Q.vertices:ℤ)*(-b)+(Q.vertices:ℤ)) : ℤ)) :
    ((M.boundedBelowMinimalResolution b hb).complex.X n).grade q = ⊥ := by
  change (E.cornerGradedRightModule Q
    (((E.cornerCoverZAlgebra Q).rightBoundedMinimalResolution M.recoveredRightModule
      ((Q.vertices:ℤ)*(-b)+(Q.vertices:ℤ))
      (M.recoveredRightModule_isZero_above_of_grade_lower_bound b hb)).complex.X n)).grade q = ⊥
  exact E.cornerGradedRightModule_grade_eq_bot_of_height_bound Q _
    ((Q.vertices:ℤ)*(-b)+(Q.vertices:ℤ))
    ((E.cornerCoverZAlgebra Q).rightBoundedMinimalResolution_term_isZero_above
      M.recoveredRightModule ((Q.vertices:ℤ)*(-b)+(Q.vertices:ℤ))
      (M.recoveredRightModule_isZero_above_of_grade_lower_bound b hb) n) q hq

theorem boundedBelowMinimalResolution_d_minimal
    (M : E.CutGradedRightModule Q) (b : ℤ)
    (hb : ∀ q : ℤ, q < b → M.grade q = ⊥) (n : ℕ) :
    IsMinimalMorphism ((M.boundedBelowMinimalResolution b hb).complex.d (n+1) n) := by
  change IsMinimalMorphism (E.cornerGradedModuleMap Q
    (((E.cornerCoverZAlgebra Q).rightBoundedMinimalResolution M.recoveredRightModule
      ((Q.vertices:ℤ)*(-b)+(Q.vertices:ℤ))
      (M.recoveredRightModule_isZero_above_of_grade_lower_bound b hb)).complex.d (n+1) n))
  exact E.cornerGradedModuleMap_minimal Q _
    ((E.cornerCoverZAlgebra Q).rightBoundedMinimalResolution_d_minimal
      M.recoveredRightModule ((Q.vertices:ℤ)*(-b)+(Q.vertices:ℤ))
      (M.recoveredRightModule_isZero_above_of_grade_lower_bound b hb) n)

theorem boundedBelowMinimalResolution_all_d_minimal
    (M : E.CutGradedRightModule Q) (b : ℤ)
    (hb : ∀ q : ℤ, q < b → M.grade q = ⊥) (i j : ℕ) :
    IsMinimalMorphism ((M.boundedBelowMinimalResolution b hb).complex.d i j) := by
  by_cases h : i = j+1
  · subst i
    exact M.boundedBelowMinimalResolution_d_minimal b hb j
  · rw [(M.boundedBelowMinimalResolution b hb).complex.shape i j (fun h' => h h'.symm)]
    intro x
    change 0 ∈ _
    exact Submodule.zero_mem _

theorem exists_boundedBelow_minimal_projectiveResolution
    (M : E.CutGradedRightModule Q) (b : ℤ)
    (hb : ∀ q : ℤ, q < b → M.grade q = ⊥) :
    ∃ P : ProjectiveResolution M, ∃ c : ℤ,
      (∀ n : ℕ, ∀ q : ℤ, q < c → (P.complex.X n).grade q = ⊥) ∧
      (∀ i j : ℕ, IsMinimalMorphism (P.complex.d i j)) :=
  ⟨M.boundedBelowMinimalResolution b hb,
    -(Int.natAbs ((Q.vertices:ℤ)*(-b)+(Q.vertices:ℤ)) : ℤ),
    M.boundedBelowMinimalResolution_grade_eq_bot b hb,
    M.boundedBelowMinimalResolution_all_d_minimal b hb⟩

end ASGinzburg.ZAlgebra.PeriodIso.CutGradedRightModule
