import ASGinzburg.PeriodCutCornerProjection
import ASGinzburg.PeriodCornerCover

/-! Projecting an actual homogeneous R block to one target vertex
is the sum of all its actual entries in that target column. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

theorem sum_cutHomogeneousComponentLinear_target
    (m : ℕ) (j : Q.Vertex)
    (r : E.CutGradedBlock (fun t : Q.Vertex => (t.val:ℤ)) m) :
    (∑ i : Q.Vertex,E.cutHomogeneousComponentLinear (fun t : Q.Vertex => (t.val:ℤ)) m i j
      (r i j))=
      E.cutVertexIdempotent (fun t : Q.Vertex => (t.val:ℤ)) j*
        E.cutHomogeneousLinearInclusion (fun t : Q.Vertex => (t.val:ℤ)) m r := by
  simp only [← E.cutHomogeneous_corner_projection (fun t : Q.Vertex => (t.val:ℤ)) m]
  rw [← Finset.mul_sum,E.sum_cutVertexIdempotent,mul_one]

end ASGinzburg.ZAlgebra.PeriodIso
