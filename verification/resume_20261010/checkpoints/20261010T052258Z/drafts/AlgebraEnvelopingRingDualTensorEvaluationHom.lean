import ASGinzburg.EnvelopingBalancedTensorHomEquiv
import work.ASGinzburgDraft.AlgebraEnvelopingRightModuleBimodule
import Mathlib.LinearAlgebra.Contraction

/-! Canonical enveloping contractions use the actual adjoint Hom action.
The first tensor factor acts by precomposition on a field dual, and the
second tensor factor acts by right multiplication on the value ring. -/
namespace ASGinzburg
open scoped TensorProduct ModuleCat.Algebra
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module Rᵐᵒᵖ M]
variable [IsScalarTower k Rᵐᵒᵖ M]
variable (X : Type z) [AddCommGroup X] [Module k X] [Module Rᵐᵒᵖ X]
variable [IsScalarTower k Rᵐᵒᵖ X]

noncomputable def envelopingTensorEvaluationHomScalarTower :
    letI := envelopingBalancedTensorHomModule k R M X
    IsScalarTower k (AlgebraEnvelopingRing k R) (BalancedTensorHom k R M X) := by
  letI := envelopingBalancedTensorHomRightModule k R M X
  letI := envelopingBalancedTensorHomRightScalarTower k R M X
  letI := envelopingBalancedTensorHomActionsCommute k R M X
  letI := envelopingBalancedTensorHomModule k R M X
  constructor
  intro c t f
  change TensorProduct.Algebra.moduleAux (c • t) f =
    c • TensorProduct.Algebra.moduleAux t f
  rw [map_smul, LinearMap.smul_apply]

noncomputable def envelopingTensorEvaluationHomScalarCommute :
    letI := envelopingBalancedTensorHomModule k R M X
    SMulCommClass (AlgebraEnvelopingRing k R) k (BalancedTensorHom k R M X) := by
  letI := envelopingBalancedTensorHomRightModule k R M X
  letI := envelopingBalancedTensorHomRightScalarTower k R M X
  letI := envelopingBalancedTensorHomActionsCommute k R M X
  letI := envelopingBalancedTensorHomModule k R M X
  constructor
  intro t c f
  change TensorProduct.Algebra.moduleAux t (c • f) =
    c • TensorProduct.Algebra.moduleAux t f
  exact (TensorProduct.Algebra.moduleAux t).map_smul c f

omit [Module Rᵐᵒᵖ M] [IsScalarTower k Rᵐᵒᵖ M]
  [Module Rᵐᵒᵖ X] [IsScalarTower k Rᵐᵒᵖ X] in
noncomputable def envelopingTensorEvaluationDualSeed :
    BalancedTensorHom k R M k →ₗ[k] BalancedTensorHom k R M R where
  toFun φ := (show M →ₗ[k] k from φ).smulRight (1 : R)
  map_add' φ ψ := by ext m; exact add_smul (φ m) (ψ m) (1 : R)
  map_smul' c φ := by ext m; exact smul_assoc c (φ m) (1 : R)

omit [Module Rᵐᵒᵖ M] [IsScalarTower k Rᵐᵒᵖ M]
  [Module Rᵐᵒᵖ X] [IsScalarTower k Rᵐᵒᵖ X] in
@[simp] theorem envelopingTensorEvaluationDualSeed_apply
    (φ : BalancedTensorHom k R M k) (m : M) :
    envelopingTensorEvaluationDualSeed k R M φ m = φ m • (1 : R) := rfl

omit [Module Rᵐᵒᵖ X] [IsScalarTower k Rᵐᵒᵖ X] in
noncomputable def envelopingTensorEvaluationContraction
    (φ : BalancedTensorHom k R M k) :
    letI := envelopingBalancedTensorHomModule k R M R
    AlgebraEnvelopingRing k R →ₗ[AlgebraEnvelopingRing k R] BalancedTensorHom k R M R := by
  letI := envelopingBalancedTensorHomModule k R M R
  exact {
    toFun := fun t => t • envelopingTensorEvaluationDualSeed k R M φ
    map_add' := fun t s => add_smul t s _
    map_smul' := fun t s => mul_smul t s _ }

omit [Module Rᵐᵒᵖ X] [IsScalarTower k Rᵐᵒᵖ X] in
@[simp] theorem envelopingTensorEvaluationContraction_tmul
    (φ : BalancedTensorHom k R M k) (a : R) (b : Rᵐᵒᵖ) (m : M) :
    letI := envelopingBalancedTensorHomModule k R M R
    envelopingTensorEvaluationContraction k R M φ (a ⊗ₜ[k] b) m =
      φ (MulOpposite.op a • m) • b.unop := by
  letI := envelopingBalancedTensorHomModule k R M R
  change ((a ⊗ₜ[k] b) • envelopingTensorEvaluationDualSeed k R M φ) m = _
  rw [envelopingBalancedTensorHomModule_tmul_apply,
    envelopingTensorEvaluationDualSeed_apply]
  change (φ (MulOpposite.op a • m) • (1 : R)) * b.unop = _
  rw [smul_mul_assoc, one_mul]

variable (P : Type*) [AddCommGroup P] [Module k P]
variable [Module (AlgebraEnvelopingRing k R) P]
variable [IsScalarTower k (AlgebraEnvelopingRing k R) P]

noncomputable def envelopingTensorEvaluationCurryEquiv :
    letI := envelopingBalancedTensorHomModule k R M X
    letI := envelopingTensorEvaluationHomScalarTower k R M X
    letI := envelopingTensorEvaluationHomScalarCommute k R M X
    letI := envelopingBalancedTensorRightModule k R M P
    letI := envelopingBalancedTensorRightScalarTower k R M P
    (P →ₗ[AlgebraEnvelopingRing k R] BalancedTensorHom k R M X) ≃ₗ[k]
      (EnvelopingBalancedTensorSpace k R M P →ₗ[Rᵐᵒᵖ] X) := by
  letI := envelopingLeftModule k R P
  letI := envelopingLeftScalarTower k R P
  letI := envelopingBalancedTensorHomModule k R M X
  letI := envelopingTensorEvaluationHomScalarTower k R M X
  letI := envelopingTensorEvaluationHomScalarCommute k R M X
  letI := envelopingBalancedTensorRightModule k R M P
  letI := envelopingBalancedTensorRightScalarTower k R M P
  exact {
    toFun := envelopingBalancedTensorUncurry k R M P X
    invFun := envelopingBalancedTensorCurry k R M P X
    left_inv := fun g => by
      apply LinearMap.ext
      intro p
      apply balancedTensorHom_ext k R M X
      intro m
      rw [envelopingBalancedTensorCurry_apply, envelopingBalancedTensorUncurry_tmul]
    right_inv := fun f => by
      apply LinearMap.ext
      intro t
      refine balancedTensorSpace_induction k R M P (fun t =>
        envelopingBalancedTensorUncurry k R M P X
          (envelopingBalancedTensorCurry k R M P X f) t = f t) ?_ ?_ ?_ t
      · simp only [map_zero]
      · intro m p
        rw [envelopingBalancedTensorUncurry_tmul, envelopingBalancedTensorCurry_apply]
      · intro a b ha hb
        rw [map_add, map_add, ha, hb]
    map_add' := fun g h => by
      apply LinearMap.ext
      intro t
      refine balancedTensorSpace_induction k R M P (fun t =>
        envelopingBalancedTensorUncurry k R M P X (g + h) t =
          (envelopingBalancedTensorUncurry k R M P X g +
            envelopingBalancedTensorUncurry k R M P X h) t) ?_ ?_ ?_ t
      · simp only [map_zero]
      · intro m p
        simp only [envelopingBalancedTensorUncurry_tmul, LinearMap.add_apply,
          balancedTensorHom_add_apply]
      · intro a b ha hb
        simp only [map_add, LinearMap.add_apply] at ha hb ⊢
        rw [ha, hb, add_add_add_comm]
    map_smul' := fun c g => by
      apply LinearMap.ext
      intro t
      refine balancedTensorSpace_induction k R M P (fun t =>
        envelopingBalancedTensorUncurry k R M P X (c • g) t =
          (c • envelopingBalancedTensorUncurry k R M P X g) t) ?_ ?_ ?_ t
      · simp only [map_zero]
      · intro m p
        simp only [envelopingBalancedTensorUncurry_tmul, LinearMap.smul_apply,
          balancedTensorHom_smul_k_apply]
      · intro a b ha hb
        simp only [map_add, LinearMap.smul_apply] at ha hb ⊢
        rw [ha, hb] }

@[simp] theorem envelopingTensorEvaluationCurryEquiv_tmul :
    letI := envelopingLeftModule k R P
    letI := envelopingBalancedTensorHomModule k R M X
    letI := envelopingTensorEvaluationHomScalarTower k R M X
    letI := envelopingTensorEvaluationHomScalarCommute k R M X
    letI := envelopingBalancedTensorRightModule k R M P
    letI := envelopingBalancedTensorRightScalarTower k R M P
    ∀ (g : P →ₗ[AlgebraEnvelopingRing k R] BalancedTensorHom k R M X)
      (m : M) (p : P),
    envelopingTensorEvaluationCurryEquiv k R M X P g
      (balancedTensorTmul k R M P m p) = g p m := by
  intros
  exact envelopingBalancedTensorUncurry_tmul k R M P X _ _ _

end ASGinzburg
