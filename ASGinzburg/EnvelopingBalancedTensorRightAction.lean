import ASGinzburg.AlgebraEnvelopingModuleRestrictions
import ASGinzburg.BalancedTensorRightMapLaws

/-! The genuine quotient N tensor_R P inherits the residual right R
action of an actual enveloping module P. -/
namespace ASGinzburg
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module Rᵐᵒᵖ M]
variable (P : Type z) [AddCommGroup P] [Module k P]
variable [Module (AlgebraEnvelopingRing k R) P] [IsScalarTower k (AlgebraEnvelopingRing k R) P]

abbrev EnvelopingBalancedTensorSpace :=
  letI := envelopingLeftModule k R P
  BalancedTensorSpace k R M P

noncomputable def envelopingBalancedTensorRightActionHom :
    Rᵐᵒᵖ →+* Module.End k (EnvelopingBalancedTensorSpace k R M P) := by
  letI := envelopingLeftModule k R P
  letI := envelopingRightModule k R P
  letI := envelopingLeftScalarTower k R P
  exact {
    toFun := fun b => balancedTensorMapRight k R M (envelopingRightOperator k R P b)
    map_zero' := by
      apply balancedTensorSpace_linearMap_ext k R M P
      intro x y
      rw [balancedTensorMapRight_tmul]
      change balancedTensorTmul k R M P x ((0 : Rᵐᵒᵖ) • y)=0
      rw [zero_smul]
      exact map_zero (balancedTensorBilinear k R M P x)
    map_one' := by
      apply balancedTensorSpace_linearMap_ext k R M P
      intro x y
      rw [balancedTensorMapRight_tmul]
      change balancedTensorTmul k R M P x ((1 : Rᵐᵒᵖ) • y)=balancedTensorTmul k R M P x y
      rw [one_smul]
    map_add' := by
      intro b c
      apply balancedTensorSpace_linearMap_ext k R M P
      intro x y
      simp only [LinearMap.add_apply,balancedTensorMapRight_tmul]
      change balancedTensorTmul k R M P x ((b+c) • y)=
        balancedTensorTmul k R M P x (b • y)+balancedTensorTmul k R M P x (c • y)
      rw [add_smul]
      exact map_add (balancedTensorBilinear k R M P x) _ _
    map_mul' := by
      intro b c
      apply balancedTensorSpace_linearMap_ext k R M P
      intro x y
      change balancedTensorMapRight k R M (envelopingRightOperator k R P (b*c))
        (balancedTensorTmul k R M P x y)=
        balancedTensorMapRight k R M (envelopingRightOperator k R P b)
          (balancedTensorMapRight k R M (envelopingRightOperator k R P c)
            (balancedTensorTmul k R M P x y))
      rw [balancedTensorMapRight_tmul,balancedTensorMapRight_tmul,balancedTensorMapRight_tmul]
      change balancedTensorTmul k R M P x ((b*c) • y)=
        balancedTensorTmul k R M P x (b • c • y)
      rw [mul_smul]}

noncomputable def envelopingBalancedTensorRightModule :
    Module Rᵐᵒᵖ (EnvelopingBalancedTensorSpace k R M P) :=
  Module.compHom _ (envelopingBalancedTensorRightActionHom k R M P)

theorem envelopingBalancedTensorRightModule_tmul (b : Rᵐᵒᵖ) (x : M) (y : P) :
    letI := envelopingLeftModule k R P
    letI := envelopingRightModule k R P
    letI := envelopingBalancedTensorRightModule k R M P
    b • balancedTensorTmul k R M P x y=balancedTensorTmul k R M P x (b • y) := by
  letI := envelopingLeftModule k R P
  letI := envelopingRightModule k R P
  letI := envelopingLeftScalarTower k R P
  letI := envelopingBalancedTensorRightModule k R M P
  exact balancedTensorMapRight_tmul k R M (envelopingRightOperator k R P b) x y

end ASGinzburg
