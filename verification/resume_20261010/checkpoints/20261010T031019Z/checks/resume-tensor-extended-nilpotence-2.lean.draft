import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Ideal.Operations

/-! Extending an ideal from either tensor factor preserves an actual
ideal-power nilpotence bound, also for noncommutative tensor factors. -/
namespace ASGinzburg
open scoped TensorProduct
universe u v w
variable {k : Type u} [Field k]
variable {R : Type v} [Ring R] [Algebra k R]
variable {S : Type w} [Ring S] [Algebra k S]

theorem tmul_mem_tensorLeftIdeal (I : Ideal R) (a : R) (ha : a ∈ I) (b : S) :
    a ⊗ₜ[k] b ∈ I.map (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S) := by
  have h := (I.map (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S)).mul_mem_left
    (1 ⊗ₜ[k] b) (Ideal.mem_map_of_mem Algebra.TensorProduct.includeLeft ha)
  simpa only [Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.tmul_mul_tmul,one_mul,mul_one] using h

theorem tmul_mem_tensorRightIdeal (I : Ideal S) (a : R) (b : S) (hb : b ∈ I) :
    a ⊗ₜ[k] b ∈ I.map (Algebra.TensorProduct.includeRight : S →ₐ[k] R ⊗[k] S) := by
  have h := (I.map (Algebra.TensorProduct.includeRight : S →ₐ[k] R ⊗[k] S)).mul_mem_left
    (a ⊗ₜ[k] 1) (Ideal.mem_map_of_mem Algebra.TensorProduct.includeRight hb)
  simpa only [Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul] using h

theorem tensorLeftIdeal_mul_le (I J : Ideal R) :
    I.map (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S) *
      J.map (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S) ≤
      (I*J).map (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S) := by
  apply Ideal.mul_le.mpr
  intro x hx y hy
  have hx' : x ∈ LinearMap.range
      (LinearMap.rTensor S (Submodule.subtype (I.restrictScalars k))) := by
    rw [← Ideal.map_includeLeft_eq]
    exact hx
  have hy' : y ∈ LinearMap.range
      (LinearMap.rTensor S (Submodule.subtype (J.restrictScalars k))) := by
    rw [← Ideal.map_includeLeft_eq]
    exact hy
  obtain ⟨x, rfl⟩ := hx'
  obtain ⟨y, rfl⟩ := hy'
  clear hx hy
  induction x with
  | zero => simp only [map_zero,zero_mul]; exact Submodule.zero_mem _
  | tmul a b =>
    induction y with
    | zero => simp only [map_zero,mul_zero]; exact Submodule.zero_mem _
    | tmul c d =>
      simp only [LinearMap.rTensor_tmul,Submodule.coe_subtype,
        Algebra.TensorProduct.tmul_mul_tmul]
      exact tmul_mem_tensorLeftIdeal (I*J) _ (Ideal.mul_mem_mul a.property c.property) _
    | add y z hy hz =>
      rw [map_add,mul_add]
      exact Submodule.add_mem _ hy hz
  | add x z hx hz =>
    rw [map_add,add_mul]
    exact Submodule.add_mem _ hx hz

theorem tensorRightIdeal_mul_le (I J : Ideal S) :
    I.map (Algebra.TensorProduct.includeRight : S →ₐ[k] R ⊗[k] S) *
      J.map (Algebra.TensorProduct.includeRight : S →ₐ[k] R ⊗[k] S) ≤
      (I*J).map (Algebra.TensorProduct.includeRight : S →ₐ[k] R ⊗[k] S) := by
  apply Ideal.mul_le.mpr
  intro x hx y hy
  have hx' : x ∈ LinearMap.range
      (LinearMap.lTensor R (Submodule.subtype (I.restrictScalars k))) := by
    rw [← Ideal.map_includeRight_eq]
    exact hx
  have hy' : y ∈ LinearMap.range
      (LinearMap.lTensor R (Submodule.subtype (J.restrictScalars k))) := by
    rw [← Ideal.map_includeRight_eq]
    exact hy
  obtain ⟨x, rfl⟩ := hx'
  obtain ⟨y, rfl⟩ := hy'
  clear hx hy
  induction x with
  | zero => simp only [map_zero,zero_mul]; exact Submodule.zero_mem _
  | tmul a b =>
    induction y with
    | zero => simp only [map_zero,mul_zero]; exact Submodule.zero_mem _
    | tmul c d =>
      simp only [LinearMap.lTensor_tmul,Submodule.coe_subtype,
        Algebra.TensorProduct.tmul_mul_tmul]
      exact tmul_mem_tensorRightIdeal (I*J) _ _ (Ideal.mul_mem_mul b.property d.property)
    | add y z hy hz =>
      rw [map_add,mul_add]
      exact Submodule.add_mem _ hy hz
  | add x z hx hz =>
    rw [map_add,add_mul]
    exact Submodule.add_mem _ hx hz

theorem tensorLeftIdeal_pow_le (I : Ideal R) (n : ℕ) :
    I.map (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S)^n ≤
      (I^n).map (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S) := by
  induction n with
  | zero => simp only [Submodule.pow_zero,Ideal.one_eq_top,Ideal.map_top]; exact le_rfl
  | succ n ih =>
    rw [Submodule.pow_succ,Submodule.pow_succ]
    exact (Ideal.mul_mono_left ih).trans (tensorLeftIdeal_mul_le (I^n) I)

theorem tensorRightIdeal_pow_le (I : Ideal S) (n : ℕ) :
    I.map (Algebra.TensorProduct.includeRight : S →ₐ[k] R ⊗[k] S)^n ≤
      (I^n).map (Algebra.TensorProduct.includeRight : S →ₐ[k] R ⊗[k] S) := by
  induction n with
  | zero => simp only [Submodule.pow_zero,Ideal.one_eq_top,Ideal.map_top]; exact le_rfl
  | succ n ih =>
    rw [Submodule.pow_succ,Submodule.pow_succ]
    exact (Ideal.mul_mono_left ih).trans (tensorRightIdeal_mul_le (I^n) I)

theorem tensorLeftIdeal_pow_eq_bot (I : Ideal R) (n : ℕ) (hI : I^n=⊥) :
    I.map (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S)^n=⊥ := by
  apply le_antisymm _ bot_le
  simpa only [hI,Ideal.map_bot] using (tensorLeftIdeal_pow_le (S:=S) I n)

theorem tensorRightIdeal_pow_eq_bot (I : Ideal S) (n : ℕ) (hI : I^n=⊥) :
    I.map (Algebra.TensorProduct.includeRight : S →ₐ[k] R ⊗[k] S)^n=⊥ := by
  apply le_antisymm _ bot_le
  simpa only [hI,Ideal.map_bot] using (tensorRightIdeal_pow_le (R:=R) I n)

end ASGinzburg
