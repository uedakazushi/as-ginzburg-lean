import ASGinzburg.BalancedTensorHom
import ASGinzburg.BalancedTensorRightMapLaws

/-! The actual noncommutative tensor-Hom equivalence: balanced k-linear
maps from M tensor_R N correspond to R-linear maps from N to Hom_k(M,P),
with the left R-action on Hom given by precomposition with right multiplication. -/
namespace ASGinzburg
universe u v w z p
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module Rᵐᵒᵖ M]
variable [IsScalarTower k Rᵐᵒᵖ M]
variable (N : Type z) [AddCommGroup N] [Module k N] [Module R N]
variable [IsScalarTower k R N]
variable (P : Type p) [AddCommGroup P] [Module k P]

noncomputable def balancedTensorCurry
    (f : BalancedTensorSpace k R M N →ₗ[k] P) :
    N →ₗ[R] BalancedTensorHom k R M P where
  toFun y := (balancedTensorHomLinearEquiv k R M P).symm
    (f.comp ((balancedTensorBilinear k R M N).flip y))
  map_add' y z := by
    apply balancedTensorHom_ext k R M P
    intro x
    change f (balancedTensorBilinear k R M N x (y+z)) =
      f (balancedTensorBilinear k R M N x y) + f (balancedTensorBilinear k R M N x z)
    rw [map_add, map_add]
  map_smul' r y := by
    apply balancedTensorHom_ext k R M P
    intro x
    change f (balancedTensorTmul k R M N x (r • y)) =
      f (balancedTensorTmul k R M N (MulOpposite.op r • x) y)
    rw [balancedTensorTmul_balance]

omit [IsScalarTower k R N] in
theorem balancedTensorCurry_apply (f : BalancedTensorSpace k R M N →ₗ[k] P)
    (y : N) (x : M) :
    balancedTensorCurry k R M N P f y x = f (balancedTensorTmul k R M N x y) := rfl

noncomputable def balancedTensorUncurryBilinear
    (g : N →ₗ[R] BalancedTensorHom k R M P) : M →ₗ[k] N →ₗ[k] P where
  toFun x :=
    { toFun := fun y => g y x
      map_add' := fun y z => by
        rw [map_add, balancedTensorHom_add_apply]
      map_smul' := fun c y => by
        change (g (c • y)) x = c • (g y) x
        rw [g.map_smul_of_tower, balancedTensorHom_smul_k_apply] }
  map_add' x z := by
    apply LinearMap.ext
    intro y
    exact (balancedTensorHomLinearEquiv k R M P (g y)).map_add x z
  map_smul' c x := by
    apply LinearMap.ext
    intro y
    exact (balancedTensorHomLinearEquiv k R M P (g y)).map_smul c x

noncomputable def balancedTensorUncurry
    (g : N →ₗ[R] BalancedTensorHom k R M P) :
    BalancedTensorSpace k R M N →ₗ[k] P :=
  balancedTensorLift k R M N (balancedTensorUncurryBilinear k R M N P g) (by
    intro r x y
    change g y (MulOpposite.op r • x) = g (r • y) x
    rw [g.map_smul, balancedTensorHom_smul_apply])

theorem balancedTensorUncurry_tmul (g : N →ₗ[R] BalancedTensorHom k R M P)
    (x : M) (y : N) :
    balancedTensorUncurry k R M N P g (balancedTensorTmul k R M N x y) = g y x := by
  rw [balancedTensorUncurry, balancedTensorLift_tmul]
  rfl

noncomputable def balancedTensorHomEquiv :
    (BalancedTensorSpace k R M N →ₗ[k] P) ≃ₗ[k]
      (N →ₗ[R] BalancedTensorHom k R M P) where
  toFun := balancedTensorCurry k R M N P
  invFun := balancedTensorUncurry k R M N P
  left_inv f := by
    apply balancedTensorSpace_linearMap_ext k R M N
    intro x y
    rw [balancedTensorUncurry_tmul, balancedTensorCurry_apply]
  right_inv g := by
    apply LinearMap.ext
    intro y
    apply balancedTensorHom_ext k R M P
    intro x
    rw [balancedTensorCurry_apply, balancedTensorUncurry_tmul]
  map_add' f g := by
    apply LinearMap.ext
    intro y
    apply balancedTensorHom_ext k R M P
    intro x
    change (f+g) (balancedTensorTmul k R M N x y) =
      f (balancedTensorTmul k R M N x y) + g (balancedTensorTmul k R M N x y)
    rfl
  map_smul' c f := by
    apply LinearMap.ext
    intro y
    apply balancedTensorHom_ext k R M P
    intro x
    change (c • f) (balancedTensorTmul k R M N x y) =
      c • f (balancedTensorTmul k R M N x y)
    rfl

end ASGinzburg
