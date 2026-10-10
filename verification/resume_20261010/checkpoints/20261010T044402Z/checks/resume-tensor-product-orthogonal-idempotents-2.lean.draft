import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Module.BigOperators

/-! Pure tensors of actual finite complete orthogonal idempotents form a
finite complete orthogonal family in the ordinary tensor product algebra.
This supplies genuine idempotent projective summands for an enveloping
algebra, whose second tensor factor is the ordinary opposite algebra. -/
namespace ASGinzburg
open scoped TensorProduct
universe u v w z z'
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (S : Type w) [Ring S] [Algebra k S]
variable {ι : Type z} {κ : Type z'} [Fintype ι] [Fintype κ]
variable (e : ι → R) (f : κ → S)

def tensorProductIdempotentFamily (a : ι × κ) : R ⊗[k] S := e a.1 ⊗ₜ[k] f a.2

omit [Fintype ι] [Fintype κ] in
theorem tensorProductIdempotentFamily_idempotent
    (he : ∀ i : ι, e i * e i = e i) (hf : ∀ j : κ, f j * f j = f j)
    (a : ι × κ) :
    tensorProductIdempotentFamily k R S e f a * tensorProductIdempotentFamily k R S e f a =
      tensorProductIdempotentFamily k R S e f a := by
  rw [tensorProductIdempotentFamily, Algebra.TensorProduct.tmul_mul_tmul, he, hf]

omit [Fintype ι] [Fintype κ] in
theorem tensorProductIdempotentFamily_orthogonal
    (he : ∀ i i' : ι, i ≠ i' → e i * e i' = 0)
    (hf : ∀ j j' : κ, j ≠ j' → f j * f j' = 0)
    (a b : ι × κ) (hab : a ≠ b) :
    tensorProductIdempotentFamily k R S e f a * tensorProductIdempotentFamily k R S e f b = 0 := by
  rw [tensorProductIdempotentFamily, tensorProductIdempotentFamily,
    Algebra.TensorProduct.tmul_mul_tmul]
  by_cases h : a.1 = b.1
  · have h' : a.2 ≠ b.2 := fun h' => hab (Prod.ext h h')
    rw [hf _ _ h', TensorProduct.tmul_zero]
  · rw [he _ _ h, TensorProduct.zero_tmul]

theorem tensorProductIdempotentFamily_sum_one
    (he : ∑ i : ι, e i = 1) (hf : ∑ j : κ, f j = 1) :
    ∑ a : ι × κ, tensorProductIdempotentFamily k R S e f a = 1 := by
  classical
  rw [Fintype.sum_prod_type]
  simp_rw [tensorProductIdempotentFamily, ← TensorProduct.tmul_sum]
  rw [← TensorProduct.sum_tmul, he, hf]
  rfl

end ASGinzburg
