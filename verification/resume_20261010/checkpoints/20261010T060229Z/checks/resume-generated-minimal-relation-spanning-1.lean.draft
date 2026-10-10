import ASGinzburg.GeneratedLinearIdeals
import ASGinzburg.MinimalRelationComponents
import ASGinzburg.FreePathDecomposableProducts

/-! In the actual directed free-path algebra, genuine ideal generators
span the genuine minimal relation quotient modulo IJ + JI. -/
namespace ASGinzburg.CutQuiver
open ZAlgebra
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]
variable (S : ∀ i j, Set ((Q.unrolledPathZAlgebra k).Hom i j))

noncomputable def generatedRelationModArrowIdeal : (Q.unrolledPathZAlgebra k).LinearIdeal where
  hom i j := Submodule.span k (S i j) ⊔ Q.relationDecomposables (LinearIdeal.generated S) i j
  comp_left := by
    intro i j l f hf g
    let I := LinearIdeal.generated S
    have hfI : f ∈ I.hom i j :=
      (sup_le (Submodule.span_le.mpr (LinearIdeal.subset_generated S i j))
        (Q.relationDecomposables_le I i j)) hf
    rcases lt_trichotomy j l with hlt | heq | hlt
    · apply Submodule.mem_sup_right
      apply Submodule.mem_sup_left
      exact I.comp_mem_mul (Q.unrolledArrowIdeal k) hfI
        (by rw [Q.unrolledArrowIdeal_off_diagonal_eq_top k j l hlt]; exact Submodule.mem_top)
    · subst l
      obtain ⟨c,rfl⟩ := (Q.unrolledPathZAlgebra k).connected j g
      simpa only [map_smul,LinearMap.smul_apply,(Q.unrolledPathZAlgebra k).comp_id] using
        Submodule.smul_mem (Submodule.span k (S i j) ⊔ Q.relationDecomposables I i j) c hf
    · rw [(Q.unrolledPathZAlgebra k).positive hlt g]
      simp
  comp_right := by
    intro i j l g hg f
    let I := LinearIdeal.generated S
    have hgI : g ∈ I.hom j l :=
      (sup_le (Submodule.span_le.mpr (LinearIdeal.subset_generated S j l))
        (Q.relationDecomposables_le I j l)) hg
    rcases lt_trichotomy i j with hlt | heq | hlt
    · apply Submodule.mem_sup_right
      apply Submodule.mem_sup_right
      exact (Q.unrolledArrowIdeal k).comp_mem_mul I
        (by rw [Q.unrolledArrowIdeal_off_diagonal_eq_top k i j hlt]; exact Submodule.mem_top) hgI
    · subst j
      obtain ⟨c,rfl⟩ := (Q.unrolledPathZAlgebra k).connected i f
      simpa only [map_smul,(Q.unrolledPathZAlgebra k).id_comp] using
        Submodule.smul_mem (Submodule.span k (S i l) ⊔ Q.relationDecomposables I i l) c hg
    · rw [(Q.unrolledPathZAlgebra k).positive hlt f,map_zero]
      exact Submodule.zero_mem _

theorem generated_hom_eq_span_sup_relationDecomposables (i j : ℤ) :
    (LinearIdeal.generated S).hom i j =
      Submodule.span k (S i j) ⊔ Q.relationDecomposables (LinearIdeal.generated S) i j := by
  apply le_antisymm
  · exact LinearIdeal.generated_le S (Q.generatedRelationModArrowIdeal k S)
      (fun i j s hs => Submodule.mem_sup_left (Submodule.subset_span hs)) i j
  · exact sup_le (Submodule.span_le.mpr (LinearIdeal.subset_generated S i j))
      (Q.relationDecomposables_le (LinearIdeal.generated S) i j)

end ASGinzburg.CutQuiver
