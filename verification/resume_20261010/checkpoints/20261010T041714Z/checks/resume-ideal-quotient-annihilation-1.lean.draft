import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! A two-sided ideal annihilates its genuine quotient left module. -/
namespace ASGinzburg
universe v
variable (R : Type v) [Ring R] (I : Ideal R) [I.IsTwoSided]

theorem idealQuotient_smul_eq_zero (r : R) (hr : r ∈ I) (q : R ⧸ I) :
    r • q = 0 := by
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
  change Ideal.Quotient.mk I (r*s) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (I.mul_mem_right s hr)

end ASGinzburg
