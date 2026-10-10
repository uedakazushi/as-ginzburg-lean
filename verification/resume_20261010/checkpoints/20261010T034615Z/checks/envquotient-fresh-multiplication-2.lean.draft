import work.ASGinzburgDraft.PeriodCutEnvelopingDegreeInclusion
import work.ASGinzburgDraft.PeriodCutEnvelopingDegreeZeroBridge
import work.ASGinzburgDraft.PeriodCutEnvelopingScalars

/-! Multiplication in the ordinary unsigned enveloping ring respects
the actual total-degree homogeneous subspaces. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open scoped TensorProduct DirectSum
universe u v w
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k} {p : ℤ}
variable (E : A.PeriodIso p) {ι : Type w} [Fintype ι] (vertex : ι → ℤ)

set_option synthInstance.maxHeartbeats 200000 in
theorem cutEnvelopingHomogeneousInclusion_mul_mem_totalDegree
    (d c : ℕ × ℕ) (x : E.CutEnvelopingBlock vertex d)
    (y : E.CutEnvelopingBlock vertex c) :
    E.cutEnvelopingHomogeneousInclusion vertex d x *
      E.cutEnvelopingHomogeneousInclusion vertex c y ∈
        E.cutEnvelopingHomogeneousSubspace vertex (d.1+d.2+(c.1+c.2)) := by
  rcases d with ⟨i,j⟩
  rcases c with ⟨m,n⟩
  let μ := Algebra.TensorProduct.mul (R := k)
    (A := E.CutGradedRing vertex) (B := (E.CutGradedRing vertex)ᵐᵒᵖ)
  change μ (E.cutEnvelopingHomogeneousInclusion vertex (i,j) x)
    (E.cutEnvelopingHomogeneousInclusion vertex (m,n) y) ∈ _
  induction x using TensorProduct.induction_on with
  | zero =>
      rw [(E.cutEnvelopingHomogeneousInclusion vertex (i,j)).map_zero,
        μ.map_zero, LinearMap.zero_apply]
      exact Submodule.zero_mem _
  | tmul a b =>
      induction y using TensorProduct.induction_on with
      | zero =>
          rw [(E.cutEnvelopingHomogeneousInclusion vertex (m,n)).map_zero,
            (μ _).map_zero]
          exact Submodule.zero_mem _
      | tmul z t =>
          change E.cutEnvelopingHomogeneousInclusion vertex (i,j) (a ⊗ₜ[k] b) *
            E.cutEnvelopingHomogeneousInclusion vertex (m,n) (z ⊗ₜ[k] t) ∈ _
          rw [E.cutEnvelopingHomogeneousInclusion_mul_tmul]
          exact E.cutEnvelopingHomogeneousInclusion_mem_totalDegree vertex _
            ⟨(i+m,n+j), by dsimp; omega⟩ _
      | add y z hy hz =>
          rw [(E.cutEnvelopingHomogeneousInclusion vertex (m,n)).map_add, (μ _).map_add]
          exact Submodule.add_mem _ hy hz
  | add x z hx hz =>
      rw [(E.cutEnvelopingHomogeneousInclusion vertex (i,j)).map_add,
        μ.map_add, LinearMap.add_apply]
      exact Submodule.add_mem _ hx hz

set_option synthInstance.maxHeartbeats 200000 in
theorem cutEnvelopingHomogeneousSubspace_mul_mem (n m : ℕ)
    {x y : AlgebraEnvelopingRing k (E.CutGradedRing vertex)}
    (hx : x ∈ E.cutEnvelopingHomogeneousSubspace vertex n)
    (hy : y ∈ E.cutEnvelopingHomogeneousSubspace vertex m) :
    x*y ∈ E.cutEnvelopingHomogeneousSubspace vertex (n+m) := by
  obtain ⟨x,rfl⟩ := hx
  obtain ⟨y,rfl⟩ := hy
  let μ := Algebra.TensorProduct.mul (R := k)
    (A := E.CutGradedRing vertex) (B := (E.CutGradedRing vertex)ᵐᵒᵖ)
  change μ (E.cutEnvelopingDegreeInclusion vertex n x)
    (E.cutEnvelopingDegreeInclusion vertex m y) ∈ _
  induction x using DirectSum.induction_on with
  | zero =>
      rw [(E.cutEnvelopingDegreeInclusion vertex n).map_zero, μ.map_zero, LinearMap.zero_apply]
      exact Submodule.zero_mem _
  | of d b =>
      induction y using DirectSum.induction_on with
      | zero =>
          rw [(E.cutEnvelopingDegreeInclusion vertex m).map_zero, (μ _).map_zero]
          exact Submodule.zero_mem _
      | of c t =>
          change E.cutEnvelopingDegreeInclusion vertex n
              (DirectSum.lof k (CutEnvelopingDegreePairs n)
                (fun d => E.CutEnvelopingBlock vertex d.val) d b) *
            E.cutEnvelopingDegreeInclusion vertex m
              (DirectSum.lof k (CutEnvelopingDegreePairs m)
                (fun c => E.CutEnvelopingBlock vertex c.val) c t) ∈ _
          rw [E.cutEnvelopingDegreeInclusion_lof, E.cutEnvelopingDegreeInclusion_lof]
          simpa only [d.property, c.property] using
            E.cutEnvelopingHomogeneousInclusion_mul_mem_totalDegree vertex d.val c.val b t
      | add y z hy hz =>
          rw [(E.cutEnvelopingDegreeInclusion vertex m).map_add, (μ _).map_add]
          exact Submodule.add_mem _ hy hz
  | add x z hx hz =>
      rw [(E.cutEnvelopingDegreeInclusion vertex n).map_add, μ.map_add, LinearMap.add_apply]
      exact Submodule.add_mem _ hx hz

variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices : ℤ))

set_option synthInstance.maxHeartbeats 200000 in
theorem cutEnvelopingZeroInclusion_mul_mem_homogeneousSubspace
    (a : AlgebraEnvelopingRing k
      (E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) 0)) (n : ℕ)
    {x : AlgebraEnvelopingRing k (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))}
    (hx : x ∈ E.cutEnvelopingHomogeneousSubspace (fun i : Q.Vertex => (i.val : ℤ)) n) :
    E.cutEnvelopingZeroInclusion Q a * x ∈
      E.cutEnvelopingHomogeneousSubspace (fun i : Q.Vertex => (i.val : ℤ)) n := by
  have ha : E.cutEnvelopingZeroInclusion Q a ∈
      E.cutEnvelopingHomogeneousSubspace (fun i : Q.Vertex => (i.val : ℤ)) 0 := by
    rw [← E.cutEnvelopingDegreeInclusion_degreeZeroEquiv Q a]
    exact E.cutEnvelopingDegreeInclusion_mem_homogeneousSubspace _ 0 _
  simpa only [Nat.zero_add] using
    E.cutEnvelopingHomogeneousSubspace_mul_mem (fun i : Q.Vertex => (i.val : ℤ)) 0 n ha hx

set_option synthInstance.maxHeartbeats 200000 in
theorem cutEnvelopingHomogeneousSubspace_mul_zeroInclusion_mem
    (a : AlgebraEnvelopingRing k
      (E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) 0)) (n : ℕ)
    {x : AlgebraEnvelopingRing k (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))}
    (hx : x ∈ E.cutEnvelopingHomogeneousSubspace (fun i : Q.Vertex => (i.val : ℤ)) n) :
    x * E.cutEnvelopingZeroInclusion Q a ∈
      E.cutEnvelopingHomogeneousSubspace (fun i : Q.Vertex => (i.val : ℤ)) n := by
  have ha : E.cutEnvelopingZeroInclusion Q a ∈
      E.cutEnvelopingHomogeneousSubspace (fun i : Q.Vertex => (i.val : ℤ)) 0 := by
    rw [← E.cutEnvelopingDegreeInclusion_degreeZeroEquiv Q a]
    exact E.cutEnvelopingDegreeInclusion_mem_homogeneousSubspace _ 0 _
  simpa only [Nat.add_zero] using
    E.cutEnvelopingHomogeneousSubspace_mul_mem (fun i : Q.Vertex => (i.val : ℤ)) n 0 hx ha

end ASGinzburg.ZAlgebra.PeriodIso
