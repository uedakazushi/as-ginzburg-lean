import work.ASGinzburgDraft.PathAutomorphismArrowSubstitution
import ASGinzburg.PathLinearIdeals

/-! The actual image of a two-sided path ideal under a genuine path
automorphism, expressed by inverse images in each preserved corner. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def VertexCutPathAutomorphism.transportIdeal
    (E : Q.VertexCutPathAutomorphism k) (I : Q.PathLinearIdeal k) : Q.PathLinearIdeal k where
  hom i j := (I.hom i j).comap
    (VertexCutPathAutomorphism.componentLinearEquiv Q k (E⁻¹) i j).toLinearMap
  comp_left := by
    intro i j l f hf g
    change VertexCutPathAutomorphism.componentLinearEquiv Q k (E⁻¹) i l
      (Q.pathComp k g f) ∈ I.hom i l
    have H := (Q.pathComponentAlgebra k).totalAlgEquivComponentLinearEquiv_comp
      (E⁻¹).val (VertexCutPathAutomorphism.fixes_vertex Q k (E⁻¹)) f g
    change VertexCutPathAutomorphism.componentLinearEquiv Q k (E⁻¹) i l
      (Q.pathComp k g f) = Q.pathComp k
        (VertexCutPathAutomorphism.componentLinearEquiv Q k (E⁻¹) j l g)
        (VertexCutPathAutomorphism.componentLinearEquiv Q k (E⁻¹) i j f) at H
    rw [H]
    exact I.comp_left hf _
  comp_right := by
    intro i j l g hg f
    change VertexCutPathAutomorphism.componentLinearEquiv Q k (E⁻¹) i l
      (Q.pathComp k g f) ∈ I.hom i l
    have H := (Q.pathComponentAlgebra k).totalAlgEquivComponentLinearEquiv_comp
      (E⁻¹).val (VertexCutPathAutomorphism.fixes_vertex Q k (E⁻¹)) f g
    change VertexCutPathAutomorphism.componentLinearEquiv Q k (E⁻¹) i l
      (Q.pathComp k g f) = Q.pathComp k
        (VertexCutPathAutomorphism.componentLinearEquiv Q k (E⁻¹) j l g)
        (VertexCutPathAutomorphism.componentLinearEquiv Q k (E⁻¹) i j f) at H
    rw [H]
    exact I.comp_right hg _

theorem VertexCutPathAutomorphism.mem_transportIdeal
    (E : Q.VertexCutPathAutomorphism k) (I : Q.PathLinearIdeal k)
    (i j : Q.Vertex) (f : Q.PathComponent k i j) :
    f ∈ (VertexCutPathAutomorphism.transportIdeal Q k E I).hom i j ↔
      VertexCutPathAutomorphism.componentLinearEquiv Q k (E⁻¹) i j f ∈ I.hom i j := Iff.rfl

theorem VertexCutPathAutomorphism.image_mem_transportIdeal
    (E : Q.VertexCutPathAutomorphism k) (I : Q.PathLinearIdeal k)
    (i j : Q.Vertex) (f : Q.PathComponent k i j) :
    VertexCutPathAutomorphism.componentLinearEquiv Q k E i j f ∈
        (VertexCutPathAutomorphism.transportIdeal Q k E I).hom i j ↔ f ∈ I.hom i j := by
  rw [VertexCutPathAutomorphism.mem_transportIdeal,
    VertexCutPathAutomorphism.componentLinearEquiv_inv, LinearEquiv.symm_apply_apply]

end ASGinzburg.CutQuiver
