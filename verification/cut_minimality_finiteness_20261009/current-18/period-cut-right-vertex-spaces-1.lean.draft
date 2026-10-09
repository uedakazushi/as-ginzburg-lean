import ASGinzburg.PeriodCutCorners

/-! The genuine right ideal e_i R is the fixed subspace of left
multiplication by the actual vertex idempotent. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

noncomputable def cutRightVertexSpace (i : Q.Vertex) :
    Submodule k (E.CutGradedRing (fun t : Q.Vertex => (t.val:ℤ))) where
  carrier := {r | E.cutVertexIdempotent (fun t : Q.Vertex => (t.val:ℤ)) i*r=r}
  zero_mem' := mul_zero _
  add_mem' := by
    intro r s hr hs
    change _*(r+s)=r+s
    rw [mul_add,hr,hs]
  smul_mem' := by
    intro c r hr
    change _*(c • r)=c • r
    rw [Algebra.mul_smul_comm,hr]

theorem cutRightVertexSpace_mul_mem (i : Q.Vertex)
    (r s : E.CutGradedRing (fun t : Q.Vertex => (t.val:ℤ)))
    (hr : r∈E.cutRightVertexSpace Q i) : r*s∈E.cutRightVertexSpace Q i := by
  change E.cutVertexIdempotent (fun t : Q.Vertex => (t.val:ℤ)) i*(r*s)=r*s
  rw [← mul_assoc,hr]

end ASGinzburg.ZAlgebra.PeriodIso
