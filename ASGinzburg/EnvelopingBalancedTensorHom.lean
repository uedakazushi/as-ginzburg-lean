import ASGinzburg.BalancedTensorHomEquiv
import ASGinzburg.AlgebraEnvelopingBimoduleMaps
import ASGinzburg.AlgebraEnvelopingModuleRestrictions

/-! The actual Hom_k(M,X) bimodule adjoint to M tensor_R (-),
where both M and X are right R modules. -/
namespace ASGinzburg
open scoped TensorProduct
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module Rᵐᵒᵖ M]
variable [IsScalarTower k Rᵐᵒᵖ M]
variable (X : Type z) [AddCommGroup X] [Module k X] [Module Rᵐᵒᵖ X]
variable [IsScalarTower k Rᵐᵒᵖ X]

noncomputable def envelopingBalancedTensorHomRightModule :
    Module Rᵐᵒᵖ (BalancedTensorHom k R M X) :=
  inferInstanceAs (Module Rᵐᵒᵖ (M →ₗ[k] X))

noncomputable def envelopingBalancedTensorHomRightScalarTower :
    letI := envelopingBalancedTensorHomRightModule k R M X
    IsScalarTower k Rᵐᵒᵖ (BalancedTensorHom k R M X) := by
  letI := envelopingBalancedTensorHomRightModule k R M X
  exact inferInstanceAs (IsScalarTower k Rᵐᵒᵖ (M →ₗ[k] X))

noncomputable def envelopingBalancedTensorHomActionsCommute :
    letI := envelopingBalancedTensorHomRightModule k R M X
    SMulCommClass R Rᵐᵒᵖ (BalancedTensorHom k R M X) := by
  letI := envelopingBalancedTensorHomRightModule k R M X
  constructor
  intro a b f
  apply balancedTensorHom_ext k R M X
  intro x
  rfl

noncomputable def envelopingBalancedTensorHomModule :
    Module (AlgebraEnvelopingRing k R) (BalancedTensorHom k R M X) := by
  letI := envelopingBalancedTensorHomRightModule k R M X
  letI := envelopingBalancedTensorHomRightScalarTower k R M X
  letI := envelopingBalancedTensorHomActionsCommute k R M X
  exact bimoduleEnvelopingModule k R (BalancedTensorHom k R M X)

theorem envelopingBalancedTensorHomModule_tmul_apply (a : R) (b : Rᵐᵒᵖ)
    (f : BalancedTensorHom k R M X) (x : M) :
    letI := envelopingBalancedTensorHomModule k R M X
    ((a ⊗ₜ[k] b) • f) x = b • f (MulOpposite.op a • x) := rfl

variable (P : Type*) [AddCommGroup P] [Module k P]
variable [Module (AlgebraEnvelopingRing k R) P]

omit [Module k P] [IsScalarTower k Rᵐᵒᵖ M] [IsScalarTower k Rᵐᵒᵖ X] in
theorem envelopingModule_tmul_smul (a : R) (b : Rᵐᵒᵖ) (p : P) :
    letI := envelopingLeftModule k R P
    letI := envelopingRightModule k R P
    (a ⊗ₜ[k] b) • p=a • b • p := by
  letI := envelopingLeftModule k R P
  letI := envelopingRightModule k R P
  change (a ⊗ₜ[k] b) • p=(a ⊗ₜ[k] (1 : Rᵐᵒᵖ)) • (((1 : R) ⊗ₜ[k] b) • p)
  rw [← mul_smul,Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]

end ASGinzburg
