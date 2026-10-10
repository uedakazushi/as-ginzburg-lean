import ASGinzburg.BalancedTensorLeftMaps
import ASGinzburg.BalancedTensorRightMaps

/-! Genuine left-module equivalences induce equivalences on the
noncommutative balanced tensor quotient, naturally in its right factor. -/
namespace ASGinzburg
universe u v w w' z z'
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module Rᵐᵒᵖ M]
variable {N : Type z} [AddCommGroup N] [Module k N] [Module R N] [IsScalarTower k R N]
variable {N' : Type z'} [AddCommGroup N'] [Module k N'] [Module R N'] [IsScalarTower k R N']

noncomputable def balancedTensorRightLinearEquiv (e : N ≃ₗ[R] N') :
    BalancedTensorSpace k R M N ≃ₗ[k] BalancedTensorSpace k R M N' where
  toFun := balancedTensorMapRight k R M e.toLinearMap
  invFun := balancedTensorMapRight k R M e.symm.toLinearMap
  left_inv x := by
    refine balancedTensorSpace_induction k R M N (fun x =>
      balancedTensorMapRight k R M e.symm.toLinearMap
        (balancedTensorMapRight k R M e.toLinearMap x) = x) ?_ ?_ ?_ x
    · simp only [map_zero]
    · intro m n
      rw [balancedTensorMapRight_tmul, balancedTensorMapRight_tmul]
      exact congrArg (balancedTensorTmul k R M N m) (e.symm_apply_apply n)
    · intro x y hx hy
      simp only [map_add, hx, hy]
  right_inv x := by
    refine balancedTensorSpace_induction k R M N' (fun x =>
      balancedTensorMapRight k R M e.toLinearMap
        (balancedTensorMapRight k R M e.symm.toLinearMap x) = x) ?_ ?_ ?_ x
    · simp only [map_zero]
    · intro m n
      rw [balancedTensorMapRight_tmul, balancedTensorMapRight_tmul]
      exact congrArg (balancedTensorTmul k R M N' m) (e.apply_symm_apply n)
    · intro x y hx hy
      simp only [map_add, hx, hy]
  map_add' := map_add _
  map_smul' := map_smul _

@[simp] theorem balancedTensorRightLinearEquiv_tmul (e : N ≃ₗ[R] N') (m : M) (n : N) :
    balancedTensorRightLinearEquiv k R M e (balancedTensorTmul k R M N m n) =
      balancedTensorTmul k R M N' m (e n) :=
  balancedTensorMapRight_tmul k R M e.toLinearMap m n

variable [IsScalarTower k Rᵐᵒᵖ M]
variable {M' : Type w'} [AddCommGroup M'] [Module k M'] [Module Rᵐᵒᵖ M']
  [IsScalarTower k Rᵐᵒᵖ M']

theorem balancedTensorRightLinearEquiv_naturality (e : N ≃ₗ[R] N')
    (f : M →ₗ[Rᵐᵒᵖ] M') :
    (balancedTensorRightLinearEquiv k R M' e).toLinearMap.comp
        (balancedTensorMapLeft k R N f) =
      (balancedTensorMapLeft k R N' f).comp
        (balancedTensorRightLinearEquiv k R M e).toLinearMap := by
  apply balancedTensorSpace_linearMap_ext
  intro m n
  change balancedTensorRightLinearEquiv k R M' e
      (balancedTensorMapLeft k R N f (balancedTensorTmul k R M N m n)) =
    balancedTensorMapLeft k R N' f
      (balancedTensorRightLinearEquiv k R M e (balancedTensorTmul k R M N m n))
  rw [balancedTensorMapLeft_tmul, balancedTensorRightLinearEquiv_tmul,
    balancedTensorRightLinearEquiv_tmul, balancedTensorMapLeft_tmul]

end ASGinzburg
