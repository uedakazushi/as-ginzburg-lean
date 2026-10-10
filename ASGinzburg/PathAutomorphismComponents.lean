import ASGinzburg.PathAutomorphismGradings

/-! Corner restrictions of actual vertex- and cut-preserving path algebra
automorphisms retain the genuine group composition. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem VertexCutPathAutomorphism.componentLinearEquiv_one (i j : Q.Vertex) :
    VertexCutPathAutomorphism.componentLinearEquiv Q k 1 i j =
      LinearEquiv.refl k (Q.PathComponent k i j) := by
  apply LinearEquiv.ext
  intro f
  change (Q.pathComponentAlgebra k).totalComponent i j f i j = f
  exact (Q.pathComponentAlgebra k).totalComponent_apply_same i j f

theorem VertexCutPathAutomorphism.componentLinearEquiv_mul_apply
    (E F : Q.VertexCutPathAutomorphism k) (i j : Q.Vertex)
    (f : Q.PathComponent k i j) :
    VertexCutPathAutomorphism.componentLinearEquiv Q k (E*F) i j f =
      VertexCutPathAutomorphism.componentLinearEquiv Q k E i j
        (VertexCutPathAutomorphism.componentLinearEquiv Q k F i j f) := by
  change E.val (F.val ((Q.pathComponentAlgebra k).totalComponent i j f)) i j =
    VertexCutPathAutomorphism.componentLinearEquiv Q k E i j
      (F.val ((Q.pathComponentAlgebra k).totalComponent i j f) i j)
  exact (VertexCutPathAutomorphism.componentLinearEquiv_projection Q k E i j
    (F.val ((Q.pathComponentAlgebra k).totalComponent i j f))).symm

theorem VertexCutPathAutomorphism.componentLinearEquiv_mul
    (E F : Q.VertexCutPathAutomorphism k) (i j : Q.Vertex) :
    VertexCutPathAutomorphism.componentLinearEquiv Q k (E*F) i j =
      (VertexCutPathAutomorphism.componentLinearEquiv Q k F i j).trans
        (VertexCutPathAutomorphism.componentLinearEquiv Q k E i j) := by
  apply LinearEquiv.ext
  intro f
  exact VertexCutPathAutomorphism.componentLinearEquiv_mul_apply Q k E F i j f

end ASGinzburg.CutQuiver
