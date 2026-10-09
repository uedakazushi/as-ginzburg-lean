import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-! A genuine ring equivalence preserves two-sided generation by
the actual image of the generating set. -/
namespace ASGinzburg
universe u v
variable {R : Type u} [Ring R] {S : Type v} [Ring S]

theorem ringEquiv_mem_twoSidedSpan_image_iff (e : R ≃+* S) (T : Set R) (x : R) :
    e x ∈ TwoSidedIdeal.span (e '' T) ↔ x ∈ TwoSidedIdeal.span T := by
  constructor
  · intro hx
    have h : TwoSidedIdeal.span (e '' T) ≤
        (TwoSidedIdeal.span T).comap e.symm := by
      apply TwoSidedIdeal.span_le.mpr
      rintro y ⟨t,ht,rfl⟩
      apply (TwoSidedIdeal.mem_comap e.symm).mpr
      rw [e.symm_apply_apply]
      exact TwoSidedIdeal.subset_span ht
    have ht := (TwoSidedIdeal.mem_comap e.symm).mp (h hx)
    rwa [e.symm_apply_apply] at ht
  · intro hx
    have h : TwoSidedIdeal.span T ≤
        (TwoSidedIdeal.span (e '' T)).comap e := by
      apply TwoSidedIdeal.span_le.mpr
      intro t ht
      apply (TwoSidedIdeal.mem_comap e).mpr
      exact TwoSidedIdeal.subset_span ⟨t,ht,rfl⟩
    exact (TwoSidedIdeal.mem_comap e).mp (h hx)

end ASGinzburg
