import work.ASGinzburgDraft.TrianglePathAutomorphismArrowMatrices
import work.ASGinzburgDraft.PathAutomorphismComponents

/-! The genuine group homomorphism obtained by taking the three actual
arrow matrices of a vertex- and cut-preserving path automorphism. -/
namespace ASGinzburg
universe u
variable (k : Type u) [Field k]

theorem trianglePathAutomorphismArrowMatrix_one (i j : triangle333.Vertex)
    (C : ArrowSpace333 k ≃ₗ[k] triangleArrowComponent k i j) :
    trianglePathAutomorphismArrowMatrix k 1 i j C = 1 := by
  apply LinearEquiv.ext
  intro a
  apply C.injective
  rw [trianglePathAutomorphismArrowMatrix_coordinates]
  change trianglePathAutomorphismArrowLinearEquiv k 1 i j (C a) = C a
  apply Subtype.ext
  rw [trianglePathAutomorphismArrowLinearEquiv_val,
    CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv_one]
  rfl

theorem trianglePathAutomorphismArrowMatrix_mul
    (E F : triangle333.VertexCutPathAutomorphism k) (i j : triangle333.Vertex)
    (C : ArrowSpace333 k ≃ₗ[k] triangleArrowComponent k i j) :
    trianglePathAutomorphismArrowMatrix k (E * F) i j C =
      trianglePathAutomorphismArrowMatrix k E i j C *
        trianglePathAutomorphismArrowMatrix k F i j C := by
  apply LinearEquiv.ext
  intro a
  apply C.injective
  simp only [LinearEquiv.mul_apply, trianglePathAutomorphismArrowMatrix_coordinates]
  apply Subtype.ext
  simp only [trianglePathAutomorphismArrowLinearEquiv_val,
    CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv_mul_apply]

noncomputable def trianglePathAutomorphismGLRestriction :
    triangle333.VertexCutPathAutomorphism k →* TriangleGL333 k where
  toFun := trianglePathAutomorphismGLTriple k
  map_one' := by
    apply Prod.ext
    · exact trianglePathAutomorphismArrowMatrix_one k 0 1 (triangleXArrowEquiv k)
    · apply Prod.ext
      · exact trianglePathAutomorphismArrowMatrix_one k 1 2 (triangleYArrowEquiv k)
      · exact trianglePathAutomorphismArrowMatrix_one k 2 0 (triangleZArrowEquiv k)
  map_mul' E F := by
    apply Prod.ext
    · exact trianglePathAutomorphismArrowMatrix_mul k E F 0 1 (triangleXArrowEquiv k)
    · apply Prod.ext
      · exact trianglePathAutomorphismArrowMatrix_mul k E F 1 2 (triangleYArrowEquiv k)
      · exact trianglePathAutomorphismArrowMatrix_mul k E F 2 0 (triangleZArrowEquiv k)

theorem trianglePathAutomorphismGLTriple_one :
    trianglePathAutomorphismGLTriple k 1 = 1 :=
  map_one (trianglePathAutomorphismGLRestriction k)

theorem trianglePathAutomorphismGLTriple_mul
    (E F : triangle333.VertexCutPathAutomorphism k) :
    trianglePathAutomorphismGLTriple k (E * F) =
      trianglePathAutomorphismGLTriple k E * trianglePathAutomorphismGLTriple k F :=
  map_mul (trianglePathAutomorphismGLRestriction k) E F

theorem trianglePathAutomorphismGLTriple_inv
    (E : triangle333.VertexCutPathAutomorphism k) :
    trianglePathAutomorphismGLTriple k (E⁻¹) =
      (trianglePathAutomorphismGLTriple k E)⁻¹ :=
  map_inv (trianglePathAutomorphismGLRestriction k) E

end ASGinzburg
