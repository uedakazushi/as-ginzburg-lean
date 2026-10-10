import work.ASGinzburgDraft.PeriodCutRadicalProjection
import work.ASGinzburgDraft.PeriodCutRecoveredRadical
import work.ASGinzburgDraft.PeriodCutRecoveredBoundedness
import work.ASGinzburgDraft.PeriodCutRecoveredZero
import work.ASGinzburgDraft.RightModuleBoundedNakayama

/-! Genuine bounded-below graded Nakayama for the native cut ring.
The finite vertex refinement converts the integer internal degree bound
to a cover height bound, where every radical action strictly increases
the finer degree. No finite generation hypothesis is required. -/
namespace ASGinzburg.ZAlgebra.PeriodIso.CutGradedRightModule
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable {Q : CutQuiver} {E : A.PeriodIso (Q.vertices:ℤ)}

theorem subsingleton_space_of_grade_lower_bound_radical_top
    (M : E.CutGradedRightModule Q) (b : ℤ)
    (hb : ∀ q : ℤ, q < b → M.grade q = ⊥)
    (hr : M.gradedRadicalActionSpan = ⊤) : Subsingleton M.space := by
  have hrad : ∀ i : ℤ,
      (E.cornerCoverZAlgebra Q).positiveActionSpan M.recoveredRightModule i = ⊤ := by
    intro i
    obtain ⟨z, rfl⟩ := Q.heightEquiv.surjective i
    apply (Submodule.eq_top_iff').mpr
    intro x
    let w := DirectSum.lof k Q.LiftVertex (E.CornerModuleSpace Q M.recoveredRightModule) z x
    have hw : w ∈
        (E.cornerGradedRightModule Q M.recoveredRightModule).gradedRadicalActionSpan := by
      apply (M.recoveredTotalEquiv_mem_radical_iff w).mp
      rw [hr]
      exact Submodule.mem_top
    have hx := E.cornerRadicalActionSpan_component_mem Q M.recoveredRightModule w hw z
    change DirectSum.component k Q.LiftVertex (E.CornerModuleSpace Q M.recoveredRightModule) z
      (DirectSum.lof k Q.LiftVertex (E.CornerModuleSpace Q M.recoveredRightModule) z x) ∈ _ at hx
    rw [DirectSum.component.lof_self] at hx
    exact hx
  have hz := (E.cornerCoverZAlgebra Q).rightModule_isZero_of_boundedAbove_radical_top
    M.recoveredRightModule ((Q.vertices:ℤ)*(-b)+(Q.vertices:ℤ))
    (M.recoveredRightModule_isZero_above_of_grade_lower_bound b hb) hrad
  exact M.recoveredRightModule_isZero_iff_subsingleton_space.mp hz

theorem subsingleton_space_of_grade_lower_bound_radical_quotient
    (M : E.CutGradedRightModule Q) (b : ℤ)
    (hb : ∀ q : ℤ, q < b → M.grade q = ⊥)
    (hQ : Subsingleton (M.space ⧸ M.gradedRadicalActionSpan)) : Subsingleton M.space :=
  M.subsingleton_space_of_grade_lower_bound_radical_top b hb
    ((Submodule.subsingleton_quotient_iff_eq_top _).mp hQ)

end ASGinzburg.ZAlgebra.PeriodIso.CutGradedRightModule
