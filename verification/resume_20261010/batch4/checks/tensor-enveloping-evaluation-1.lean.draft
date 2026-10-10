import work.ASGinzburgDraft.AlgebraEnvelopingRingDualTensorEvaluationShuffle
import work.ASGinzburgDraft.AlgebraEnvelopingRingDualTensorEvaluationField

/-! Genuine finite-projective enveloping tensor evaluation. Every
comparison is constructed from the actual balanced quotient and actual
module actions. Finiteness of the right module is over the original
field; projectivity and finiteness of the term are over the enveloping
ring. -/
namespace ASGinzburg
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u v
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]

attribute [local instance 2100] ordinaryRingDualTensorModuleK
attribute [local instance 2100] ordinaryRingDualTensorScalarTower
attribute [local instance 3500] ordinaryRingDualTensorFieldSMulK

variable (M : ModuleCat.{v} Rᵐᵒᵖ) [Module.Finite k M]
variable {P : ModuleCat.{v} (AlgebraEnvelopingRing k R)}

noncomputable def envelopingFiniteProjectiveRingDualTensorEquiv
    (hP : ordinaryFiniteProjectiveProperty (AlgebraEnvelopingRing k R) P) :
    letI := envelopingTensorEvaluationRestrictedRightModule k R
      (ordinaryRingDual (AlgebraEnvelopingRing k R) P)
    letI : SMul Rᵐᵒᵖ (ordinaryRingDual (AlgebraEnvelopingRing k R) P) :=
      envelopingTensorEvaluationRestrictedRightSMul k R
        (ordinaryRingDual (AlgebraEnvelopingRing k R) P)
    letI := envelopingBalancedTensorRightModule k R M P
    letI := envelopingBalancedTensorRightScalarTower k R M P
    BalancedTensorSpace k R (ordinaryRingDual (AlgebraEnvelopingRing k R) P)
      (BalancedTensorHom k R M k) ≃ₗ[k]
        (EnvelopingBalancedTensorSpace k R M P →ₗ[Rᵐᵒᵖ] R) := by
  letI := envelopingTensorEvaluationRestrictedRightModule k R
    (ordinaryRingDual (AlgebraEnvelopingRing k R) P)
  letI : SMul Rᵐᵒᵖ (ordinaryRingDual (AlgebraEnvelopingRing k R) P) :=
    envelopingTensorEvaluationRestrictedRightSMul k R
      (ordinaryRingDual (AlgebraEnvelopingRing k R) P)
  letI := envelopingBalancedTensorHomModule k R M R
  letI := envelopingTensorEvaluationHomScalarTower k R M R
  letI := envelopingTensorEvaluationHomScalarCommute k R M R
  letI := envelopingBalancedTensorRightModule k R M P
  letI := envelopingBalancedTensorRightScalarTower k R M P
  exact (envelopingTensorEvaluationShuffleEquiv k R M
    (ordinaryRingDual (AlgebraEnvelopingRing k R) P)).trans
      ((ordinaryFiniteProjectiveRingDualTensorFieldEquiv k (AlgebraEnvelopingRing k R)
        (BalancedTensorHom k R M R) hP).trans
          (envelopingTensorEvaluationCurryEquiv k R M R P))

@[simp] theorem envelopingFiniteProjectiveRingDualTensorEquiv_tmul
    (hP : ordinaryFiniteProjectiveProperty (AlgebraEnvelopingRing k R) P)
    (f : ordinaryRingDual (AlgebraEnvelopingRing k R) P)
    (φ : BalancedTensorHom k R M k) (m : M) (p : P) :
    letI := envelopingTensorEvaluationRestrictedRightModule k R
      (ordinaryRingDual (AlgebraEnvelopingRing k R) P)
    letI : SMul Rᵐᵒᵖ (ordinaryRingDual (AlgebraEnvelopingRing k R) P) :=
      envelopingTensorEvaluationRestrictedRightSMul k R
        (ordinaryRingDual (AlgebraEnvelopingRing k R) P)
    letI := envelopingLeftModule k R P
    letI := envelopingBalancedTensorHomModule k R M R
    letI := envelopingBalancedTensorRightModule k R M P
    letI := envelopingBalancedTensorRightScalarTower k R M P
    envelopingFiniteProjectiveRingDualTensorEquiv k R M hP
      (balancedTensorTmul k R (ordinaryRingDual (AlgebraEnvelopingRing k R) P)
        (BalancedTensorHom k R M k) f φ) (balancedTensorTmul k R M P m p) =
        envelopingTensorEvaluationContraction k R M φ (f p) m := by
  letI := envelopingTensorEvaluationRestrictedRightModule k R
    (ordinaryRingDual (AlgebraEnvelopingRing k R) P)
  letI : SMul Rᵐᵒᵖ (ordinaryRingDual (AlgebraEnvelopingRing k R) P) :=
    envelopingTensorEvaluationRestrictedRightSMul k R
      (ordinaryRingDual (AlgebraEnvelopingRing k R) P)
  letI := envelopingLeftModule k R P
  letI := envelopingBalancedTensorHomModule k R M R
  letI := envelopingTensorEvaluationHomScalarTower k R M R
  letI := envelopingTensorEvaluationHomScalarCommute k R M R
  letI := envelopingBalancedTensorRightModule k R M P
  letI := envelopingBalancedTensorRightScalarTower k R M P
  change envelopingTensorEvaluationCurryEquiv k R M R P
    (ordinaryFiniteProjectiveRingDualTensorFieldEquiv k (AlgebraEnvelopingRing k R)
      (BalancedTensorHom k R M R) hP
      (envelopingTensorEvaluationShuffle k R M
        (ordinaryRingDual (AlgebraEnvelopingRing k R) P)
        (balancedTensorTmul k R (ordinaryRingDual (AlgebraEnvelopingRing k R) P)
          (BalancedTensorHom k R M k) f φ)))
    (balancedTensorTmul k R M P m p) = _
  rw [envelopingTensorEvaluationShuffle_tmul, envelopingTensorEvaluationCurryEquiv_tmul,
    ordinaryFiniteProjectiveRingDualTensorFieldEquiv_tmul]
  rfl

end ASGinzburg
