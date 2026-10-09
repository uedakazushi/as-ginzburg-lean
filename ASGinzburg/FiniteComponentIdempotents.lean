import ASGinzburg.FiniteComponentEmbeddings
import Mathlib.LinearAlgebra.Pi

/-! Genuine linear matrix component embeddings and a complete finite
family of orthogonal idempotents in the actual convolution ring. -/
namespace ASGinzburg.LinearComponentAlgebra
universe u v
variable {k : Type u} [Field k] {ι : Type v} [Fintype ι]
  (B : LinearComponentAlgebra k ι)

noncomputable def totalComponentLinear (i j : ι) : B.Hom i j →ₗ[k] B.Total := by
  classical
  exact (LinearMap.single k (fun r => ∀ s, B.Hom r s) i).comp
    (LinearMap.single k (fun s => B.Hom i s) j)

omit [Fintype ι] in
@[simp] theorem totalComponentLinear_apply (i j : ι) (a : B.Hom i j) :
    B.totalComponentLinear i j a=B.totalComponent i j a := rfl

noncomputable def totalIdempotent (i : ι) : B.Total := B.totalComponent i i (B.id i)

theorem totalIdempotent_mul_self (i : ι) : B.totalIdempotent i*B.totalIdempotent i=
    B.totalIdempotent i := by
  rw [totalIdempotent,B.totalComponent_mul_same,B.comp_id]

theorem totalIdempotent_mul_ne (i j : ι) (h : i≠j) :
    B.totalIdempotent i*B.totalIdempotent j=0 :=
  B.totalComponent_mul_of_ne i i j j (B.id i) (B.id j) h

theorem sum_totalIdempotent : (∑ i : ι, B.totalIdempotent i)=1 := B.sum_totalComponent_id

theorem totalIdempotent_mul_component (i j : ι) (a : B.Hom i j) :
    B.totalIdempotent j*B.totalComponent i j a=B.totalComponent i j a := by
  rw [totalIdempotent,B.totalComponent_mul_same,B.comp_id]

theorem totalComponent_mul_idempotent (i j : ι) (a : B.Hom i j) :
    B.totalComponent i j a*B.totalIdempotent i=B.totalComponent i j a := by
  rw [totalIdempotent,B.totalComponent_mul_same,B.id_comp]

end ASGinzburg.LinearComponentAlgebra
