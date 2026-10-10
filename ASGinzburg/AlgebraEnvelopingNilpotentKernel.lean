import ASGinzburg.AlgebraEnvelopingMap
import ASGinzburg.TensorExtendedIdealNilpotence
import ASGinzburg.NoncommNilpotentIdealSum

/-! A surjective algebra map with an actually nilpotent kernel has an
actually nilpotent kernel on its unsigned enveloping algebra. The bound
is doubled because the enveloping kernel has two tensor-factor ideals. -/
namespace ASGinzburg
open scoped TensorProduct
universe u v w
variable (k : Type u) [Field k]
variable {R : Type v} [Ring R] [Algebra k R]
variable {S : Type w} [Ring S] [Algebra k S]
variable (f : R →ₐ[k] S)

theorem algebraHom_opKernel_pow_mem_unop (n : ℕ) :
    ∀ x : Rᵐᵒᵖ, x ∈ (RingHom.ker f.op)^n →
      x.unop ∈ (RingHom.ker f)^n := by
  induction n with
  | zero =>
    intro x _
    rw [Submodule.pow_zero,Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ n ih =>
    intro x hx
    rw [Submodule.pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      rw [Ideal.IsTwoSided.pow_succ]
      change b.unop*a.unop ∈ RingHom.ker f * (RingHom.ker f)^n
      have hb' : b.unop ∈ RingHom.ker f := by
        change f b.unop=0
        exact congrArg MulOpposite.unop (RingHom.mem_ker.mp hb)
      exact Ideal.mul_mem_mul hb' (ih a ha)
    · intro a b ha hb
      change a.unop+b.unop ∈ (RingHom.ker f)^(n+1)
      exact Submodule.add_mem _ ha hb

theorem algebraHom_opKernel_pow_eq_bot (n : ℕ) (hn : (RingHom.ker f)^n=⊥) :
    (RingHom.ker f.op)^n=⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  change x=0
  apply MulOpposite.unop_injective
  change x.unop=0
  simpa only [hn,Submodule.mem_bot] using algebraHom_opKernel_pow_mem_unop k f n x hx

theorem algebraEnvelopingMapKernel_pow_eq_bot
    (hf : Function.Surjective f) (n : ℕ) (hn : (RingHom.ker f)^n=⊥) :
    (algebraEnvelopingMapKernel k f)^(2*n)=⊥ := by
  let L : Ideal (AlgebraEnvelopingRing k R) :=
    (RingHom.ker f).map
      (Algebra.TensorProduct.includeLeft : R →ₐ[k] AlgebraEnvelopingRing k R)
  let J : Ideal (AlgebraEnvelopingRing k R) :=
    (RingHom.ker f.op).map
      (Algebra.TensorProduct.includeRight : Rᵐᵒᵖ →ₐ[k] AlgebraEnvelopingRing k R)
  letI : L.IsTwoSided := by
    dsimp [L]
    rw [← Algebra.TensorProduct.rTensor_ker f hf]
    infer_instance
  letI : J.IsTwoSided := by
    dsimp [J]
    rw [← Algebra.TensorProduct.lTensor_ker f.op (algebraHom_op_surjective k f hf)]
    infer_instance
  have hL : L^n=⊥ := tensorLeftIdeal_pow_eq_bot (S:=Rᵐᵒᵖ) (RingHom.ker f) n hn
  have hJ : J^n=⊥ := tensorRightIdeal_pow_eq_bot (R:=R) (RingHom.ker f.op) n
    (algebraHom_opKernel_pow_eq_bot k f n hn)
  rw [algebraEnvelopingMapKernel_eq_sup k f hf]
  simpa only [Nat.two_mul] using noncommIdealSup_pow_eq_bot L J n n hL hJ

end ASGinzburg
