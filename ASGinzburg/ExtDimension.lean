import Mathlib.Tactic
import Mathlib.Data.Finsupp.Order

/-!
# The numerical step in Proposition 1.3

This file proves a statement about finitely supported dimension tables.
It does not identify a table with Ext of an unrolled algebra, or prove that
the distinguished Ext group is nonzero. Those homological steps are not
implicit assumptions disguised as conclusions.
-/

namespace ASGinzburg

universe u

noncomputable def totalDimension {I : Type u} (d : I →₀ ℕ) : ℕ :=
  d.sum fun _ n => n

theorem dimension_table_eq_single {I : Type u} (d : I →₀ ℕ) (i : I)
    (hi : d i = 1) (htotal : totalDimension d = 1) :
    d = Finsupp.single i 1 := by
  classical
  have hmem : i ∈ d.support := by simp [Finsupp.mem_support_iff, hi]
  have hsum : ∑ j ∈ d.support.erase i, d j = 0 := by
    have heq := Finset.sum_erase_add d.support (fun j => d j) hmem
    dsimp only at heq
    change (∑ j ∈ d.support, d j) = 1 at htotal
    rw [hi, htotal] at heq
    omega
  ext j
  by_cases hji : j = i
  · subst j
    simp [hi]
  · have hj : d j = 0 := by
      by_cases hjmem : j ∈ d.support
      · have hjerase : j ∈ d.support.erase i := Finset.mem_erase.mpr ⟨hji, hjmem⟩
        have hle := Finset.single_le_sum (fun (x : I) (_ : x ∈ d.support.erase i) =>
          Nat.zero_le (d x)) hjerase
        rw [hsum] at hle
        omega
      · simpa [Finsupp.mem_support_iff] using hjmem
    simp [hj, hji]

theorem total_dimension_single {I : Type u} (i : I) :
    totalDimension (Finsupp.single i 1) = 1 := by
  classical
  simp [totalDimension]

theorem total_one_iff_single {I : Type u} (d : I →₀ ℕ) (i : I) (hi : d i = 1) :
    totalDimension d = 1 ↔ d = Finsupp.single i 1 := by
  constructor
  · exact dimension_table_eq_single d i hi
  · intro h
    rw [h]
    exact total_dimension_single i

/-- The pointwise conclusion in (1.11), conditional on its nonzero Ext term. -/
theorem ext_dimension_delta {V : Type u} [DecidableEq V] (d : (ℕ × V) →₀ ℕ) (v : V)
    (h3 : d (3, v) = 1) (htotal : totalDimension d = 1) (p : ℕ) (u : V) :
    d (p, u) = if (3, v) = (p, u) then 1 else 0 := by
  classical
  rw [dimension_table_eq_single d (3, v) h3 htotal]
  rw [Finsupp.single_apply]

end ASGinzburg
