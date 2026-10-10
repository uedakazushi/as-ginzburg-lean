import ASGinzburg.MinimalRelationComponents
import ASGinzburg.UnrolledPathZAlgebra

/-! In sheet zero, genuine ideal products have a finite foundation
middle index. Directedness makes every product outside the finite
foundation interval zero; no ideal-support assumption is imposed. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

def foundationIdealProductGenerators (I J : (Q.unrolledPathZAlgebra k).LinearIdeal)
    (i j : Q.Vertex) : Set ((Q.unrolledPathZAlgebra k).Hom (i.val : ℤ) (j.val : ℤ)) :=
  {x | ∃ l : Q.Vertex,
    ∃ f ∈ I.hom (i.val : ℤ) (l.val : ℤ),
    ∃ g ∈ J.hom (l.val : ℤ) (j.val : ℤ), (Q.unrolledPathZAlgebra k).comp g f = x}

theorem foundationIdealProduct_eq_span (I J : (Q.unrolledPathZAlgebra k).LinearIdeal)
    (i j : Q.Vertex) :
    (I.mul J).hom (i.val : ℤ) (j.val : ℤ) =
      Submodule.span k (Q.foundationIdealProductGenerators k I J i j) := by
  change Submodule.span k
    (ZAlgebra.LinearIdeal.productGenerators I J (i.val : ℤ) (j.val : ℤ)) = _
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨l, f, hf, g, hg, rfl⟩
    by_cases hil : (i.val : ℤ) ≤ l
    · by_cases hlj : l ≤ (j.val : ℤ)
      · have hl₀ : 0 ≤ l := by omega
        have hln : l.toNat < Q.vertices := by
          have hcast := Int.toNat_of_nonneg hl₀
          have hj := j.isLt
          omega
        obtain ⟨v, hv⟩ : ∃ v : Q.Vertex, (v.val : ℤ) = l :=
          ⟨⟨l.toNat, hln⟩, Int.toNat_of_nonneg hl₀⟩
        subst l
        exact Submodule.subset_span ⟨v, f, hf, g, hg, rfl⟩
      · have hg₀ := (Q.unrolledPathZAlgebra k).positive (lt_of_not_ge hlj) g
        rw [hg₀]
        simp
    · have hf₀ := (Q.unrolledPathZAlgebra k).positive (lt_of_not_ge hil) f
      rw [hf₀, map_zero]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro x ⟨l, f, hf, g, hg, rfl⟩
    exact Submodule.subset_span ⟨(l.val : ℤ), f, hf, g, hg, rfl⟩

def foundationRelationProductGenerators (I : (Q.unrolledPathZAlgebra k).LinearIdeal)
    (i j : Q.Vertex) : Set ((Q.unrolledPathZAlgebra k).Hom (i.val : ℤ) (j.val : ℤ)) :=
  Q.foundationIdealProductGenerators k I (Q.unrolledArrowIdeal k) i j ∪
    Q.foundationIdealProductGenerators k (Q.unrolledArrowIdeal k) I i j

theorem foundationRelationDecomposables_eq_span (I : (Q.unrolledPathZAlgebra k).LinearIdeal)
    (i j : Q.Vertex) :
    Q.relationDecomposables I (i.val : ℤ) (j.val : ℤ) =
      Submodule.span k (Q.foundationRelationProductGenerators k I i j) := by
  rw [relationDecomposables, Q.foundationIdealProduct_eq_span,
    Q.foundationIdealProduct_eq_span, foundationRelationProductGenerators,
    Submodule.span_union]

end ASGinzburg.CutQuiver
