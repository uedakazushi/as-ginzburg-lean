import ASGinzburg.PeriodCutEnvelopingVertexIdempotents
import ASGinzburg.PeriodCutEnvelopingDegreeInclusion
import ASGinzburg.PeriodCutEnvelopingIntegerHomogeneousSubspaces

/-! Every actual pair-vertex idempotent belongs to the genuine
degree-zero enveloping component. Thus its principal projective summand
inherits the ordinary grading needed for a minimal graded cover. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open scoped TensorProduct
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices : ℤ))

theorem cutEnvelopingVertexIdempotent_mem_degreeZero (a : Q.Vertex × Q.Vertex) :
    E.cutEnvelopingVertexIdempotent Q a ∈
      E.cutEnvelopingHomogeneousSubspace (fun i : Q.Vertex => (i.val : ℤ)) 0 := by
  let x := E.cutMatrixComponent (fun i : Q.Vertex => (i.val : ℤ)) 0 a.1 a.1
    (E.cutGradedId (a.1.val : ℤ))
  let y := E.cutMatrixComponent (fun i : Q.Vertex => (i.val : ℤ)) 0 a.2 a.2
    (E.cutGradedId (a.2.val : ℤ))
  have h := E.cutEnvelopingHomogeneousInclusion_mem_totalDegree
    (fun i : Q.Vertex => (i.val : ℤ)) 0 ⟨(0,0),rfl⟩ (x ⊗ₜ[k] y)
  rw [E.cutEnvelopingHomogeneousInclusion_tmul] at h
  exact h

theorem cutEnvelopingVertexIdempotent_mem_integerDegreeZero (a : Q.Vertex × Q.Vertex) :
    E.cutEnvelopingVertexIdempotent Q a ∈
      E.cutEnvelopingIntegerHomogeneousSubspace (fun i : Q.Vertex => (i.val : ℤ)) 0 := by
  rw [show (0 : ℤ) = ((0:ℕ):ℤ) from rfl,
    E.cutEnvelopingIntegerHomogeneousSubspace_natCast]
  exact E.cutEnvelopingVertexIdempotent_mem_degreeZero Q a

end ASGinzburg.ZAlgebra.PeriodIso
