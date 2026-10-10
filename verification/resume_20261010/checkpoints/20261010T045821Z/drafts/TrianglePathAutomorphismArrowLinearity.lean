import work.ASGinzburgDraft.PathAutomorphismGradings
import ASGinzburg.Triangle333

/-! On the actual three-vertex quiver, preserving vertices and the cut
grading forces every arrow substitution to be linear in actual arrows. -/
namespace ASGinzburg
universe u
variable (k : Type u) [Field k]

def triangleArrowComponent (i j : triangle333.Vertex) :
    Submodule k (triangle333.PathComponent k i j) :=
  Finsupp.supported k k {p : triangle333.Path i j | p.length = 1}

theorem triangleArrowComponent_eq_winding (i j : triangle333.Vertex) :
    triangleArrowComponent k i j = triangle333.pathWindingComponent k i j 1 := by
  unfold triangleArrowComponent CutQuiver.pathWindingComponent
  congr 1
  ext p
  change p.length = 1 ↔ p.winding = 1
  rw [triangle_path_winding]
  omega

theorem trianglePathAutomorphism_preserves_arrowComponent
    (E : triangle333.VertexCutPathAutomorphism k) (i j : triangle333.Vertex)
    (f : triangle333.PathComponent k i j) :
    f ∈ triangleArrowComponent k i j ↔
      CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k E i j f ∈
        triangleArrowComponent k i j := by
  rw [triangleArrowComponent_eq_winding]
  exact CutQuiver.VertexCutPathAutomorphism.component_preserves_winding
    triangle333 k E i j 1 f

noncomputable def trianglePathAutomorphismArrowLinearEquiv
    (E : triangle333.VertexCutPathAutomorphism k) (i j : triangle333.Vertex) :
    triangleArrowComponent k i j ≃ₗ[k] triangleArrowComponent k i j where
  toFun f := ⟨CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k E i j f.val,
    (trianglePathAutomorphism_preserves_arrowComponent k E i j f.val).mp f.property⟩
  invFun f := ⟨CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k (E⁻¹) i j f.val,
    (trianglePathAutomorphism_preserves_arrowComponent k (E⁻¹) i j f.val).mp f.property⟩
  left_inv f := by
    apply Subtype.ext
    change CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k (E⁻¹) i j
      (CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k E i j f.val) = f.val
    rw [CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv_inv]
    exact LinearEquiv.symm_apply_apply _ _
  right_inv f := by
    apply Subtype.ext
    change CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k E i j
      (CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k (E⁻¹) i j f.val) = f.val
    rw [CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv_inv]
    exact LinearEquiv.apply_symm_apply _ _
  map_add' f g := by
    apply Subtype.ext
    exact map_add (CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k E i j) f.val g.val
  map_smul' c f := by
    apply Subtype.ext
    exact map_smul (CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k E i j) c f.val

@[simp] theorem trianglePathAutomorphismArrowLinearEquiv_val
    (E : triangle333.VertexCutPathAutomorphism k) (i j : triangle333.Vertex)
    (f : triangleArrowComponent k i j) :
    (trianglePathAutomorphismArrowLinearEquiv k E i j f).val =
      CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k E i j f.val := rfl

theorem trianglePathAutomorphism_arrow_image_length_one
    (E : triangle333.VertexCutPathAutomorphism k) (a : triangle333.Arrow) :
    CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k E
        (triangle333.source a) (triangle333.target a)
        (Finsupp.single (CutQuiver.Path.snoc (.nil (triangle333.source a)) a rfl) 1) ∈
      triangleArrowComponent k (triangle333.source a) (triangle333.target a) := by
  apply (trianglePathAutomorphism_preserves_arrowComponent k E _ _ _).mp
  apply Finsupp.single_mem_supported
  simp [CutQuiver.Path.length]

end ASGinzburg
