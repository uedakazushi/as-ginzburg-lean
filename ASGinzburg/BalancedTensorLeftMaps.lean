import ASGinzburg.BalancedTensorUniversal
import Mathlib.LinearAlgebra.BilinearMap

/-! Actual right R-linear maps induce maps in the left tensor factor. -/
namespace ASGinzburg
universe u v w w' z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable {M : Type w} [AddCommGroup M] [Module k M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k Rᵐᵒᵖ M]
variable {M' : Type w'} [AddCommGroup M'] [Module k M'] [Module Rᵐᵒᵖ M']
  [IsScalarTower k Rᵐᵒᵖ M']
variable (N : Type z) [AddCommGroup N] [Module k N] [Module R N]

noncomputable def balancedTensorMapLeft (f : M →ₗ[Rᵐᵒᵖ] M') :
    BalancedTensorSpace k R M N →ₗ[k] BalancedTensorSpace k R M' N :=
  balancedTensorLift k R M N
    ((balancedTensorBilinear k R M' N).comp (f.restrictScalars k)) (by
      intro r x y
      change balancedTensorTmul k R M' N (f (MulOpposite.op r • x)) y =
        balancedTensorTmul k R M' N (f x) (r • y)
      rw [f.map_smul]
      exact balancedTensorTmul_balance k R M' N r (f x) y)

theorem balancedTensorMapLeft_tmul (f : M →ₗ[Rᵐᵒᵖ] M') (x : M) (y : N) :
    balancedTensorMapLeft k R N f (balancedTensorTmul k R M N x y) =
      balancedTensorTmul k R M' N (f x) y := by
  rw [balancedTensorMapLeft, balancedTensorLift_tmul]
  rfl

end ASGinzburg
