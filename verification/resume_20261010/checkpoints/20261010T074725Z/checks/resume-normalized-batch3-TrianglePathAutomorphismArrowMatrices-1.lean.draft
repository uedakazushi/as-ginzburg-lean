import work.ASGinzburgDraft.TriangleArrowCoordinates
import work.ASGinzburgDraft.TriangleTensorAction

/-! Coordinate extraction from an actual vertex- and cut-preserving path
algebra automorphism to the three arrow-space general linear groups. -/
namespace ASGinzburg
universe u
variable (k : Type u) [Field k]

noncomputable def trianglePathAutomorphismArrowMatrix
    (E : triangle333.VertexCutPathAutomorphism k) (i j : triangle333.Vertex)
    (C : ArrowSpace333 k ≃ₗ[k] triangleArrowComponent k i j) :
    ArrowSpace333 k ≃ₗ[k] ArrowSpace333 k :=
  (C.trans (trianglePathAutomorphismArrowLinearEquiv k E i j)).trans C.symm

theorem trianglePathAutomorphismArrowMatrix_coordinates
    (E : triangle333.VertexCutPathAutomorphism k) (i j : triangle333.Vertex)
    (C : ArrowSpace333 k ≃ₗ[k] triangleArrowComponent k i j) (a : ArrowSpace333 k) :
    C (trianglePathAutomorphismArrowMatrix k E i j C a) =
      trianglePathAutomorphismArrowLinearEquiv k E i j (C a) := by
  simp [trianglePathAutomorphismArrowMatrix]

noncomputable def trianglePathAutomorphismGLTriple
    (E : triangle333.VertexCutPathAutomorphism k) : TriangleGL333 k :=
  ⟨trianglePathAutomorphismArrowMatrix k E 0 1 (triangleXArrowEquiv k),
    trianglePathAutomorphismArrowMatrix k E 1 2 (triangleYArrowEquiv k),
    trianglePathAutomorphismArrowMatrix k E 2 0 (triangleZArrowEquiv k)⟩

theorem trianglePathAutomorphismGLTriple_X_coordinates
    (E : triangle333.VertexCutPathAutomorphism k) (a : ArrowSpace333 k) :
    (triangleXArrowEquiv k ((trianglePathAutomorphismGLTriple k E).1 a)).val =
      CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k E 0 1
        (triangleXArrowEquiv k a).val :=
  congrArg Subtype.val
    (trianglePathAutomorphismArrowMatrix_coordinates k E 0 1 (triangleXArrowEquiv k) a)

theorem trianglePathAutomorphismGLTriple_Y_coordinates
    (E : triangle333.VertexCutPathAutomorphism k) (a : ArrowSpace333 k) :
    (triangleYArrowEquiv k ((trianglePathAutomorphismGLTriple k E).2.1 a)).val =
      CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k E 1 2
        (triangleYArrowEquiv k a).val :=
  congrArg Subtype.val
    (trianglePathAutomorphismArrowMatrix_coordinates k E 1 2 (triangleYArrowEquiv k) a)

theorem trianglePathAutomorphismGLTriple_Z_coordinates
    (E : triangle333.VertexCutPathAutomorphism k) (a : ArrowSpace333 k) :
    (triangleZArrowEquiv k ((trianglePathAutomorphismGLTriple k E).2.2 a)).val =
      CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k E 2 0
        (triangleZArrowEquiv k a).val :=
  congrArg Subtype.val
    (trianglePathAutomorphismArrowMatrix_coordinates k E 2 0 (triangleZArrowEquiv k) a)

theorem trianglePathAutomorphismGLTriple_X_single
    (E : triangle333.VertexCutPathAutomorphism k) (i : Fin 3) (a : k) :
    CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k E 0 1
        (Finsupp.single (triangleXPath i) a) =
      (triangleXArrowEquiv k
        ((trianglePathAutomorphismGLTriple k E).1 (Pi.single i a))).val := by
  simpa only [triangleXArrowEquiv_single] using
    (trianglePathAutomorphismGLTriple_X_coordinates k E (Pi.single i a)).symm

theorem trianglePathAutomorphismGLTriple_Y_single
    (E : triangle333.VertexCutPathAutomorphism k) (i : Fin 3) (a : k) :
    CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k E 1 2
        (Finsupp.single (triangleYPath i) a) =
      (triangleYArrowEquiv k
        ((trianglePathAutomorphismGLTriple k E).2.1 (Pi.single i a))).val := by
  simpa only [triangleYArrowEquiv_single] using
    (trianglePathAutomorphismGLTriple_Y_coordinates k E (Pi.single i a)).symm

theorem trianglePathAutomorphismGLTriple_Z_single
    (E : triangle333.VertexCutPathAutomorphism k) (i : Fin 3) (a : k) :
    CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k E 2 0
        (Finsupp.single (triangleZPath i) a) =
      (triangleZArrowEquiv k
        ((trianglePathAutomorphismGLTriple k E).2.2 (Pi.single i a))).val := by
  simpa only [triangleZArrowEquiv_single] using
    (trianglePathAutomorphismGLTriple_Z_coordinates k E (Pi.single i a)).symm

end ASGinzburg
