import ASGinzburg.OrdinaryRingDualTensorEvaluationFinite
import ASGinzburg.BalancedTensorLeftFieldModuleChange

/-! The proved equality of the canonical algebra field action and a
compatible given field action transports genuine tensor evaluation. -/
namespace ASGinzburg
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u v
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]

noncomputable def ordinaryRingDualTensorFieldSMulK (P : ModuleCat.{v} R) :
    SMul k (ordinaryRingDual R P) := (ordinaryRingDualTensorModuleK k R P).toSMul

attribute [local instance 2100] ordinaryRingDualTensorModuleK
attribute [local instance 2100] ordinaryRingDualTensorScalarTower
attribute [local instance 3500] ordinaryRingDualTensorFieldSMulK

variable (N : Type v) [AddCommGroup N] [fieldModule : Module k N] [Module R N]
variable [IsScalarTower k R N]

noncomputable def ordinaryFiniteProjectiveRingDualTensorFieldEquiv
    {P : ModuleCat.{v} R} (hP : ordinaryFiniteProjectiveProperty R P) :
    BalancedTensorSpace k R (ordinaryRingDual R P) N ≃ₗ[k] (P →ₗ[R] N) := by
  have hfield := algebraModuleCompHomField_eq k R N
  cases hfield
  exact ordinaryFiniteProjectiveRingDualTensorEquiv k R (ModuleCat.of R N) hP

@[simp] theorem ordinaryFiniteProjectiveRingDualTensorFieldEquiv_tmul
    {P : ModuleCat.{v} R} (hP : ordinaryFiniteProjectiveProperty R P)
    (f : ordinaryRingDual R P) (y : N) (x : P) :
    ordinaryFiniteProjectiveRingDualTensorFieldEquiv k R N hP
      (balancedTensorTmul k R (ordinaryRingDual R P) N f y) x = f x • y := by
  have hfield := algebraModuleCompHomField_eq k R N
  cases hfield
  exact ordinaryFiniteProjectiveRingDualTensorEquiv_tmul k R (ModuleCat.of R N) hP f y x

end ASGinzburg
