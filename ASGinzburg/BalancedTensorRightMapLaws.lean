import ASGinzburg.BalancedTensorRightMaps

namespace ASGinzburg
universe u v w z z' z''
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module Rᵐᵒᵖ M]
variable {N : Type z} [AddCommGroup N] [Module k N] [Module R N] [IsScalarTower k R N]
variable {N' : Type z'} [AddCommGroup N'] [Module k N'] [Module R N'] [IsScalarTower k R N']
variable {N'' : Type z''} [AddCommGroup N''] [Module k N''] [Module R N''] [IsScalarTower k R N'']

theorem balancedTensorMapRight_id :
    balancedTensorMapRight k R M (LinearMap.id : N →ₗ[R] N)=LinearMap.id := by
  apply balancedTensorSpace_linearMap_ext k R M N
  intro x y
  rw [balancedTensorMapRight_tmul]
  rfl

theorem balancedTensorMapRight_comp (f : N →ₗ[R] N') (g : N' →ₗ[R] N'') :
    balancedTensorMapRight k R M (g.comp f)=
      (balancedTensorMapRight k R M g).comp (balancedTensorMapRight k R M f) := by
  apply balancedTensorSpace_linearMap_ext k R M N
  intro x y
  simp only [balancedTensorMapRight_tmul,LinearMap.comp_apply]

theorem balancedTensorMapRight_add (f g : N →ₗ[R] N') :
    balancedTensorMapRight k R M (f+g)=balancedTensorMapRight k R M f+balancedTensorMapRight k R M g := by
  apply balancedTensorSpace_linearMap_ext k R M N
  intro x y
  simp only [balancedTensorMapRight_tmul,LinearMap.add_apply]
  exact (balancedTensorBilinear k R M N' x).map_add (f y) (g y)

theorem balancedTensorMapRight_smul [SMulCommClass R k N'] (c : k) (g : N →ₗ[R] N') :
    balancedTensorMapRight k R M (c • g)=c • balancedTensorMapRight k R M g := by
  apply balancedTensorSpace_linearMap_ext k R M N
  intro x y
  simp only [balancedTensorMapRight_tmul,LinearMap.smul_apply]
  exact (balancedTensorBilinear k R M N' x).map_smul c (g y)

end ASGinzburg
