import ASGinzburg.ASPresentationQuotient

/-! In the actual positively directed free path algebra, the square
of the arrow ideal is exactly the span of strict intermediate products. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem unrolledArrowIdeal_off_diagonal_eq_top (i j : ℤ) (hij : i<j) :
    (Q.unrolledArrowIdeal k).hom i j=⊤ := by
  apply top_unique
  intro f _
  apply (Finsupp.mem_supported k f).mpr
  intro p _
  have hp : p.length≠0 := by
    intro hp
    have h := p.height_eq_of_length_zero hp
    simp only [Q.height_heightEquiv_symm] at h
    omega
  exact Nat.one_le_iff_ne_zero.mpr hp

theorem unrolledArrowIdeal_member_eq_zero_of_not_lt (i j : ℤ) (hij : j ≤ i)
    (f : (Q.unrolledPathZAlgebra k).Hom i j)
    (hf : f∈(Q.unrolledArrowIdeal k).hom i j) : f=0 := by
  rcases lt_or_eq_of_le hij with hlt|heq
  · exact (Q.unrolledPathZAlgebra k).positive hlt f
  · subst j
    rw [Q.unrolledPathIdeal_diagonal_eq_bot k 1 (by decide)] at hf
    exact hf

theorem unrolledArrowIdeal_square_eq_products_span (i j : ℤ) :
    ((Q.unrolledArrowIdeal k).mul (Q.unrolledArrowIdeal k)).hom i j=
      Submodule.span k ((Q.unrolledPathZAlgebra k).products i j) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨l,f,hf,g,hg,rfl⟩
    by_cases hil : i<l
    · by_cases hlj : l<j
      · exact Submodule.subset_span ⟨l,hil,hlj,f,g,rfl⟩
      · have hg0 := Q.unrolledArrowIdeal_member_eq_zero_of_not_lt k l j (le_of_not_gt hlj) g hg
        rw [hg0]
        simp
    · have hf0 := Q.unrolledArrowIdeal_member_eq_zero_of_not_lt k i l (le_of_not_gt hil) f hf
      rw [hf0,map_zero]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨l,hil,hlj,f,g,rfl⟩
    apply Submodule.subset_span
    refine ⟨l,f,?_,g,?_,rfl⟩
    · rw [Q.unrolledArrowIdeal_off_diagonal_eq_top k i l hil]
      exact Submodule.mem_top
    · rw [Q.unrolledArrowIdeal_off_diagonal_eq_top k l j hlj]
      exact Submodule.mem_top

end ASGinzburg.CutQuiver
