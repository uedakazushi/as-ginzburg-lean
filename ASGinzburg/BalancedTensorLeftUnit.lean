import ASGinzburg.BalancedTensorUniversal
import Mathlib.Algebra.Algebra.Tower

/-! The genuine unit isomorphism R tensor_R N ≃ N for the concrete
noncommutative balanced tensor product. -/
namespace ASGinzburg
open scoped TensorProduct
universe u v w
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (N : Type w) [AddCommGroup N] [Module k N] [Module R N]
variable [SMulCommClass k R N] [IsScalarTower k R N]

noncomputable def balancedTensorLeftUnitMap : BalancedTensorSpace k R R N →ₗ[k] N :=
  balancedTensorLift k R R N (Algebra.lsmul k k N).toLinearMap
    (fun r x y => mul_smul x r y)

noncomputable def balancedTensorLeftUnitInverse : N →ₗ[k] BalancedTensorSpace k R R N :=
  (balancedTensorRelations k R R N).mkQ.comp (TensorProduct.mk k R N 1)

noncomputable def balancedTensorLeftUnitEquiv : BalancedTensorSpace k R R N ≃ₗ[k] N where
  toFun := balancedTensorLeftUnitMap k R N
  invFun := balancedTensorLeftUnitInverse k R N
  left_inv z := by
    refine balancedTensorSpace_induction k R R N
      (fun z => balancedTensorLeftUnitInverse k R N (balancedTensorLeftUnitMap k R N z)=z)
      ?_ ?_ ?_ z
    · change balancedTensorLeftUnitInverse k R N (balancedTensorLeftUnitMap k R N 0)=0
      rw [map_zero,map_zero]
    · intro r y
      rw [balancedTensorLeftUnitMap,balancedTensorLift_tmul]
      change balancedTensorTmul k R R N 1 (r • y)=balancedTensorTmul k R R N r y
      have h := balancedTensorTmul_balance k R R N r 1 y
      change balancedTensorTmul k R R N (1*r) y=balancedTensorTmul k R R N 1 (r • y) at h
      simpa only [one_mul] using h.symm
    · intro a b ha hb
      rw [map_add,map_add,ha,hb]
  right_inv y := by
    change balancedTensorLeftUnitMap k R N (balancedTensorTmul k R R N 1 y)=y
    rw [balancedTensorLeftUnitMap,balancedTensorLift_tmul]
    exact one_smul R y
  map_add' := map_add (balancedTensorLeftUnitMap k R N)
  map_smul' := map_smul (balancedTensorLeftUnitMap k R N)

end ASGinzburg
