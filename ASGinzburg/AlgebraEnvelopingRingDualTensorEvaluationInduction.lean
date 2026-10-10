import ASGinzburg.AlgebraEnvelopingRingDualTensorEvaluationHom

/-! The actual induced field-dual module is Hom_k(M,R). The inverse is
the ordinary finite-dimensional field tensor-Hom inverse followed by
the canonical insertion of the second enveloping tensor factor. -/
namespace ASGinzburg
open scoped TensorProduct ModuleCat.Algebra
universe u v w
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module Rᵐᵒᵖ M]
variable [IsScalarTower k Rᵐᵒᵖ M]

noncomputable def envelopingTensorEvaluationFirstRightModule :
    Module Rᵐᵒᵖ (AlgebraEnvelopingRing k R) :=
  rightEnvelopingRightModule k R (AlgebraEnvelopingRing k R)

attribute [local instance 2200] envelopingTensorEvaluationFirstRightModule

noncomputable def envelopingTensorEvaluationFirstRightSMul :
    SMul Rᵐᵒᵖ (AlgebraEnvelopingRing k R) :=
  (envelopingTensorEvaluationFirstRightModule k R).toSMul

attribute [local instance 3000] envelopingTensorEvaluationFirstRightSMul

noncomputable def envelopingTensorEvaluationInductionBilinear :
    letI := envelopingBalancedTensorHomModule k R M R
    letI := envelopingTensorEvaluationHomScalarTower k R M R
    letI := envelopingTensorEvaluationHomScalarCommute k R M R
    AlgebraEnvelopingRing k R →ₗ[k] BalancedTensorHom k R M k →ₗ[k]
      BalancedTensorHom k R M R := by
  letI := envelopingBalancedTensorHomModule k R M R
  letI := envelopingTensorEvaluationHomScalarTower k R M R
  letI := envelopingTensorEvaluationHomScalarCommute k R M R
  exact {
    toFun := fun t => (Algebra.lsmul k k (BalancedTensorHom k R M R) t).comp
      (envelopingTensorEvaluationDualSeed k R M)
    map_add' := fun t s => by
      apply LinearMap.ext
      intro φ
      change (t+s) • envelopingTensorEvaluationDualSeed k R M φ =
        t • envelopingTensorEvaluationDualSeed k R M φ +
          s • envelopingTensorEvaluationDualSeed k R M φ
      exact add_smul t s _
    map_smul' := fun c t => by
      apply LinearMap.ext
      intro φ
      change (c • t) • envelopingTensorEvaluationDualSeed k R M φ =
        c • (t • envelopingTensorEvaluationDualSeed k R M φ)
      exact smul_assoc c t _ }

theorem envelopingTensorEvaluationInductionBilinear_balance (a : R)
    (t : AlgebraEnvelopingRing k R) (φ : BalancedTensorHom k R M k) :
    letI := envelopingBalancedTensorHomModule k R M R
    letI := envelopingTensorEvaluationHomScalarTower k R M R
    letI := envelopingTensorEvaluationHomScalarCommute k R M R
    envelopingTensorEvaluationInductionBilinear k R M (MulOpposite.op a • t) φ =
      envelopingTensorEvaluationInductionBilinear k R M t (a • φ) := by
  letI := envelopingBalancedTensorHomModule k R M R
  letI := envelopingTensorEvaluationHomScalarTower k R M R
  letI := envelopingTensorEvaluationHomScalarCommute k R M R
  refine TensorProduct.inductionOn (motive := fun t =>
    envelopingTensorEvaluationInductionBilinear k R M (MulOpposite.op a • t) φ =
      envelopingTensorEvaluationInductionBilinear k R M t (a • φ)) t ?_ ?_
  · intro x y
    apply balancedTensorHom_ext k R M R
    intro m
    change envelopingTensorEvaluationContraction k R M φ
      ((x ⊗ₜ[k] y) * (a ⊗ₜ[k] (1 : Rᵐᵒᵖ))) m =
      envelopingTensorEvaluationContraction k R M (a • φ) (x ⊗ₜ[k] y) m
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      envelopingTensorEvaluationContraction_tmul,
      envelopingTensorEvaluationContraction_tmul, balancedTensorHom_smul_apply,
      MulOpposite.op_mul, mul_smul]
  · intro t s ht hs
    change envelopingTensorEvaluationInductionBilinear k R M
      ((t+s) * (a ⊗ₜ[k] (1 : Rᵐᵒᵖ))) φ =
      envelopingTensorEvaluationInductionBilinear k R M (t+s) (a • φ)
    rw [add_mul, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply]
    exact congrArg₂ (· + ·) ht hs

noncomputable def envelopingTensorEvaluationInduction :
    letI := envelopingBalancedTensorHomModule k R M R
    letI := envelopingTensorEvaluationHomScalarTower k R M R
    letI := envelopingTensorEvaluationHomScalarCommute k R M R
    BalancedTensorSpace k R (AlgebraEnvelopingRing k R) (BalancedTensorHom k R M k) →ₗ[k]
      BalancedTensorHom k R M R := by
  letI := envelopingBalancedTensorHomModule k R M R
  letI := envelopingTensorEvaluationHomScalarTower k R M R
  letI := envelopingTensorEvaluationHomScalarCommute k R M R
  exact balancedTensorLift k R (AlgebraEnvelopingRing k R) (BalancedTensorHom k R M k)
    (envelopingTensorEvaluationInductionBilinear k R M)
    (envelopingTensorEvaluationInductionBilinear_balance k R M)

@[simp] theorem envelopingTensorEvaluationInduction_tmul
    (t : AlgebraEnvelopingRing k R) (φ : BalancedTensorHom k R M k) :
    letI := envelopingBalancedTensorHomModule k R M R
    letI := envelopingTensorEvaluationHomScalarTower k R M R
    letI := envelopingTensorEvaluationHomScalarCommute k R M R
    envelopingTensorEvaluationInduction k R M
      (balancedTensorTmul k R (AlgebraEnvelopingRing k R) (BalancedTensorHom k R M k) t φ) =
      envelopingTensorEvaluationContraction k R M φ t := by
  letI := envelopingBalancedTensorHomModule k R M R
  letI := envelopingTensorEvaluationHomScalarTower k R M R
  letI := envelopingTensorEvaluationHomScalarCommute k R M R
  rfl

noncomputable def envelopingTensorEvaluationSecondInsertion :
    R →ₗ[k] AlgebraEnvelopingRing k R :=
  (TensorProduct.mk k R Rᵐᵒᵖ (1 : R)).comp (MulOpposite.opLinearEquiv k).toLinearMap

noncomputable def envelopingTensorEvaluationFieldTensorSection :
    Module.Dual k M ⊗[k] R →ₗ[k]
      BalancedTensorSpace k R (AlgebraEnvelopingRing k R) (BalancedTensorHom k R M k) :=
  TensorProduct.lift ((balancedTensorBilinear k R (AlgebraEnvelopingRing k R)
    (BalancedTensorHom k R M k)).flip.compl₂
      (envelopingTensorEvaluationSecondInsertion k R))

@[simp] theorem envelopingTensorEvaluationFieldTensorSection_tmul
    (φ : Module.Dual k M) (y : R) :
    envelopingTensorEvaluationFieldTensorSection k R M (φ ⊗ₜ[k] y) =
      balancedTensorTmul k R (AlgebraEnvelopingRing k R) (BalancedTensorHom k R M k)
        ((1 : R) ⊗ₜ[k] MulOpposite.op y) φ := by
  rfl

theorem envelopingTensorEvaluationInduction_field_section
    (z : Module.Dual k M ⊗[k] R) :
    letI := envelopingBalancedTensorHomModule k R M R
    letI := envelopingTensorEvaluationHomScalarTower k R M R
    letI := envelopingTensorEvaluationHomScalarCommute k R M R
    envelopingTensorEvaluationInduction k R M
      (envelopingTensorEvaluationFieldTensorSection k R M z) = dualTensorHom k M R z := by
  letI := envelopingBalancedTensorHomModule k R M R
  letI := envelopingTensorEvaluationHomScalarTower k R M R
  letI := envelopingTensorEvaluationHomScalarCommute k R M R
  refine TensorProduct.inductionOn (motive := fun z =>
    envelopingTensorEvaluationInduction k R M
      (envelopingTensorEvaluationFieldTensorSection k R M z) = dualTensorHom k M R z)
    z ?_ ?_
  · intro φ y
    change envelopingTensorEvaluationContraction k R M φ
      ((1 : R) ⊗ₜ[k] MulOpposite.op y) = dualTensorHom k M R (φ ⊗ₜ[k] y)
    apply balancedTensorHom_ext k R M R
    intro m
    calc
      _ = φ (MulOpposite.op (1 : R) • m) • (MulOpposite.op y).unop :=
        envelopingTensorEvaluationContraction_tmul k R M φ 1 (MulOpposite.op y) m
      _ = φ m • y := by rw [MulOpposite.op_one, one_smul, MulOpposite.unop_op]
      _ = _ := rfl
  · intro x y hx hy
    rw [map_add, map_add, map_add, hx, hy]
    rfl

variable [Module.Finite k M]

noncomputable def envelopingTensorEvaluationInductionInverse :
    BalancedTensorHom k R M R →ₗ[k]
      BalancedTensorSpace k R (AlgebraEnvelopingRing k R) (BalancedTensorHom k R M k) :=
  (envelopingTensorEvaluationFieldTensorSection k R M).comp
    (dualTensorHomEquiv k M R).symm.toLinearMap

theorem envelopingTensorEvaluationInduction_inverse
    (g : BalancedTensorHom k R M R) :
    letI := envelopingBalancedTensorHomModule k R M R
    letI := envelopingTensorEvaluationHomScalarTower k R M R
    letI := envelopingTensorEvaluationHomScalarCommute k R M R
    envelopingTensorEvaluationInduction k R M
      (envelopingTensorEvaluationInductionInverse k R M g) = g := by
  letI := envelopingBalancedTensorHomModule k R M R
  letI := envelopingTensorEvaluationHomScalarTower k R M R
  letI := envelopingTensorEvaluationHomScalarCommute k R M R
  change envelopingTensorEvaluationInduction k R M
    (envelopingTensorEvaluationFieldTensorSection k R M
      ((dualTensorHomEquiv k M R).symm g)) = g
  rw [envelopingTensorEvaluationInduction_field_section]
  exact (dualTensorHomEquiv k M R).apply_symm_apply g

theorem envelopingTensorEvaluationInductionInverse_induction
    (z : BalancedTensorSpace k R (AlgebraEnvelopingRing k R) (BalancedTensorHom k R M k)) :
    letI := envelopingBalancedTensorHomModule k R M R
    letI := envelopingTensorEvaluationHomScalarTower k R M R
    letI := envelopingTensorEvaluationHomScalarCommute k R M R
    envelopingTensorEvaluationInductionInverse k R M
      (envelopingTensorEvaluationInduction k R M z) = z := by
  letI := envelopingBalancedTensorHomModule k R M R
  letI := envelopingTensorEvaluationHomScalarTower k R M R
  letI := envelopingTensorEvaluationHomScalarCommute k R M R
  refine balancedTensorSpace_induction k R (AlgebraEnvelopingRing k R)
    (BalancedTensorHom k R M k) (fun z => envelopingTensorEvaluationInductionInverse k R M
      (envelopingTensorEvaluationInduction k R M z) = z) ?_ ?_ ?_ z
  · simp only [map_zero]
  · intro t φ
    refine TensorProduct.inductionOn (motive := fun t =>
      envelopingTensorEvaluationInductionInverse k R M
        (envelopingTensorEvaluationInduction k R M
          (balancedTensorTmul k R (AlgebraEnvelopingRing k R) (BalancedTensorHom k R M k) t φ)) =
        balancedTensorTmul k R (AlgebraEnvelopingRing k R) (BalancedTensorHom k R M k) t φ)
      t ?_ ?_
    · intro a b
      have hc : envelopingTensorEvaluationContraction k R M φ (a ⊗ₜ[k] b) =
          dualTensorHomEquiv k M R ((a • φ) ⊗ₜ[k] b.unop) := by
        apply balancedTensorHom_ext k R M R
        intro m
        rw [envelopingTensorEvaluationContraction_tmul]
        change φ (MulOpposite.op a • m) • b.unop = (a • φ) m • b.unop
        rfl
      rw [envelopingTensorEvaluationInduction_tmul, hc]
      change envelopingTensorEvaluationFieldTensorSection k R M
        ((dualTensorHomEquiv k M R).symm
          (dualTensorHomEquiv k M R ((a • φ) ⊗ₜ[k] b.unop))) = _
      rw [LinearEquiv.symm_apply_apply]
      change balancedTensorTmul k R (AlgebraEnvelopingRing k R) (BalancedTensorHom k R M k)
        ((1 : R) ⊗ₜ[k] b) (a • φ) =
        balancedTensorTmul k R (AlgebraEnvelopingRing k R) (BalancedTensorHom k R M k)
          (a ⊗ₜ[k] b) φ
      rw [← balancedTensorTmul_balance]
      congr 1
      change ((1 : R) ⊗ₜ[k] b) * (a ⊗ₜ[k] (1 : Rᵐᵒᵖ)) = a ⊗ₜ[k] b
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    · intro t s ht hs
      change envelopingTensorEvaluationInductionInverse k R M
        (envelopingTensorEvaluationInduction k R M
          ((balancedTensorBilinear k R _ _).flip φ (t+s))) =
        (balancedTensorBilinear k R _ _).flip φ (t+s)
      rw [map_add, map_add, map_add]
      exact congrArg₂ (· + ·) ht hs
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]

noncomputable def envelopingTensorEvaluationInductionEquiv :
    letI := envelopingBalancedTensorHomModule k R M R
    letI := envelopingTensorEvaluationHomScalarTower k R M R
    letI := envelopingTensorEvaluationHomScalarCommute k R M R
    BalancedTensorSpace k R (AlgebraEnvelopingRing k R) (BalancedTensorHom k R M k) ≃ₗ[k]
      BalancedTensorHom k R M R := by
  letI := envelopingBalancedTensorHomModule k R M R
  letI := envelopingTensorEvaluationHomScalarTower k R M R
  letI := envelopingTensorEvaluationHomScalarCommute k R M R
  exact {
    toFun := envelopingTensorEvaluationInduction k R M
    invFun := envelopingTensorEvaluationInductionInverse k R M
    left_inv := envelopingTensorEvaluationInductionInverse_induction k R M
    right_inv := envelopingTensorEvaluationInduction_inverse k R M
    map_add' := map_add _
    map_smul' := map_smul _ }

end ASGinzburg
