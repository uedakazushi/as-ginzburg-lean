import work.ASGinzburgDraft.GeneratedMinimalRelationSpanning

/-! Actual ideal generators span the actual minimal relation quotient. -/
namespace ASGinzburg.CutQuiver
open ZAlgebra
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]
variable (S : ∀ i j, Set ((Q.unrolledPathZAlgebra k).Hom i j))

noncomputable def generatedRelationElement (i j : ℤ) (s : S i j) :
    (LinearIdeal.generated S).hom i j :=
  ⟨s.val, LinearIdeal.subset_generated S i j s.property⟩

noncomputable def generatedMinimalRelationClass (i j : ℤ) (s : S i j) :
    Q.MinimalRelationComponent (LinearIdeal.generated S) i j :=
  Submodule.Quotient.mk (Q.generatedRelationElement k S i j s)

theorem generatedRelationElement_decomposition (i j : ℤ) :
    Submodule.span k (Set.range (Q.generatedRelationElement k S i j)) ⊔
      Submodule.comap ((LinearIdeal.generated S).hom i j).subtype
        (Q.relationDecomposables (LinearIdeal.generated S) i j) = ⊤ := by
  let I := LinearIdeal.generated S
  apply Submodule.map_injective_of_injective (I.hom i j).injective_subtype
  rw [Submodule.map_sup, Submodule.map_span, Submodule.map_comap_subtype,
    inf_eq_right.mpr (Q.relationDecomposables_le I i j), Submodule.map_top,
    Submodule.range_subtype, ← Set.range_comp]
  have h : (I.hom i j).subtype ∘ Q.generatedRelationElement k S i j =
      ((↑) : S i j → (Q.unrolledPathZAlgebra k).Hom i j) := rfl
  rw [h]
  have hr : Set.range ((↑) : S i j → (Q.unrolledPathZAlgebra k).Hom i j) = S i j := by
    ext x
    exact ⟨fun ⟨s, hs⟩ => hs ▸ s.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  rw [hr]
  exact (Q.generated_hom_eq_span_sup_relationDecomposables k S i j).symm

set_option synthInstance.maxHeartbeats 200000 in
theorem generatedMinimalRelationClass_span (i j : ℤ) :
    Submodule.span k (Set.range (Q.generatedMinimalRelationClass k S i j)) = ⊤ := by
  let I := LinearIdeal.generated S
  let D := Submodule.comap (I.hom i j).subtype (Q.relationDecomposables I i j)
  have h := (D.map_mkQ_eq_top _).mpr
    (by simpa only [sup_comm] using Q.generatedRelationElement_decomposition k S i j)
  rw [Submodule.map_span, ← Set.range_comp] at h
  exact h

end ASGinzburg.CutQuiver
