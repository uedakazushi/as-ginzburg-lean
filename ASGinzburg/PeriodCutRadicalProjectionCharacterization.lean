import ASGinzburg.PeriodCutRadicalProjection

/-! The native ring radical product is exactly the finite-support family
of the cover's genuine positive-action components. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices : ℤ))

theorem cornerRadicalActionSpan_mem_iff_components
    (M : (E.cornerCoverZAlgebra Q).RightModule) (w : E.CornerModuleTotalSpace Q M) :
    w ∈ (E.cornerGradedRightModule Q M).gradedRadicalActionSpan ↔
      ∀ x : Q.LiftVertex, DirectSum.component k Q.LiftVertex (E.CornerModuleSpace Q M) x w ∈
        (E.cornerCoverZAlgebra Q).positiveActionSpan M (Q.heightEquiv x) := by
  constructor
  · intro hw x
    exact E.cornerRadicalActionSpan_component_mem Q M w hw x
  · intro h
    classical
    rw [← DirectSum.sum_support_of w]
    apply Submodule.sum_mem
    intro x hx
    exact E.cornerPositiveActionSpan_lof_mem_radical Q M x (w x) (h x)

theorem cornerRadicalActionSpan_eq_top_iff_components
    (M : (E.cornerCoverZAlgebra Q).RightModule) :
    (E.cornerGradedRightModule Q M).gradedRadicalActionSpan = ⊤ ↔
      ∀ x : Q.LiftVertex,
        (E.cornerCoverZAlgebra Q).positiveActionSpan M (Q.heightEquiv x) = ⊤ := by
  constructor
  · intro h x
    apply (Submodule.eq_top_iff').mpr
    intro w
    have hw : DirectSum.lof k Q.LiftVertex (E.CornerModuleSpace Q M) x w ∈
        (E.cornerGradedRightModule Q M).gradedRadicalActionSpan := by
      rw [h]
      exact Submodule.mem_top
    have hp := E.cornerRadicalActionSpan_component_mem Q M _ hw x
    classical
    simpa only [DirectSum.component.lof_self] using hp
  · intro h
    apply (Submodule.eq_top_iff').mpr
    intro w
    apply (E.cornerRadicalActionSpan_mem_iff_components Q M w).mpr
    intro x
    rw [h x]
    exact Submodule.mem_top

end ASGinzburg.ZAlgebra.PeriodIso
