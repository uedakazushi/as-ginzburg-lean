import ASGinzburg.BalancedTensorUniversal
import Mathlib.Algebra.Algebra.Tower

/-! The actual balanced tensor with the regular left module is the
original right module, by its genuine right action. -/
namespace ASGinzburg
universe u v w
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module Rᵐᵒᵖ M]
  [SMulCommClass k Rᵐᵒᵖ M] [IsScalarTower k Rᵐᵒᵖ M]

noncomputable def balancedTensorRightUnitBilinear : M →ₗ[k] R →ₗ[k] M where
  toFun x :=
    { toFun := fun r => MulOpposite.op r • x
      map_add' r s := by rw [MulOpposite.op_add, add_smul]
      map_smul' c r := by rw [MulOpposite.op_smul, smul_assoc]; rfl }
  map_add' x y := by ext r; exact smul_add (MulOpposite.op r) x y
  map_smul' c x := by ext r; exact (smul_comm c (MulOpposite.op r) x).symm

noncomputable def balancedTensorRightUnitMap : BalancedTensorSpace k R M R →ₗ[k] M :=
  balancedTensorLift k R M R (balancedTensorRightUnitBilinear k R M) (by
    intro r x y
    change MulOpposite.op y • (MulOpposite.op r • x) = MulOpposite.op (r*y) • x
    rw [MulOpposite.op_mul, mul_smul])

noncomputable def balancedTensorRightUnitInverse : M →ₗ[k] BalancedTensorSpace k R M R :=
  (balancedTensorBilinear k R M R).flip 1

@[simp] theorem balancedTensorRightUnitMap_tmul (x : M) (r : R) :
    balancedTensorRightUnitMap k R M (balancedTensorTmul k R M R x r) =
      MulOpposite.op r • x := by
  rw [balancedTensorRightUnitMap, balancedTensorLift_tmul]
  rfl

omit [SMulCommClass k Rᵐᵒᵖ M] [IsScalarTower k Rᵐᵒᵖ M] in
@[simp] theorem balancedTensorRightUnitInverse_apply (x : M) :
    balancedTensorRightUnitInverse k R M x = balancedTensorTmul k R M R x 1 := rfl

noncomputable def balancedTensorRightUnitEquiv : BalancedTensorSpace k R M R ≃ₗ[k] M where
  toFun := balancedTensorRightUnitMap k R M
  invFun := balancedTensorRightUnitInverse k R M
  left_inv z := by
    refine balancedTensorSpace_induction k R M R
      (fun z => balancedTensorRightUnitInverse k R M (balancedTensorRightUnitMap k R M z)=z)
      ?_ ?_ ?_ z
    · change balancedTensorRightUnitInverse k R M (balancedTensorRightUnitMap k R M 0)=0
      rw [map_zero, map_zero]
    · intro x r
      rw [balancedTensorRightUnitMap_tmul, balancedTensorRightUnitInverse_apply]
      have h := balancedTensorTmul_balance k R M R r x 1
      simpa only [smul_eq_mul, mul_one] using h
    · intro a b ha hb
      rw [map_add,map_add,ha,hb]
  right_inv x := by
    rw [balancedTensorRightUnitInverse_apply, balancedTensorRightUnitMap_tmul,
      MulOpposite.op_one, one_smul]
  map_add' := map_add (balancedTensorRightUnitMap k R M)
  map_smul' := map_smul (balancedTensorRightUnitMap k R M)

end ASGinzburg
