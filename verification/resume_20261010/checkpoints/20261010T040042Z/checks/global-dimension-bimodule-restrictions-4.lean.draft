import ASGinzburg.AlgebraEnvelopingRegularModule

/-! Every actual left module over R tensor R-op carries its genuine
commuting left R and right R actions by restriction along the two
canonical tensor inclusions. -/
namespace ASGinzburg
open scoped TensorProduct
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (P : Type w) [AddCommGroup P] [Module k P]
variable [Module (AlgebraEnvelopingRing k R) P] [IsScalarTower k (AlgebraEnvelopingRing k R) P]

noncomputable def envelopingLeftModule : Module R P :=
  Module.compHom P (Algebra.TensorProduct.includeLeft : R →ₐ[k] AlgebraEnvelopingRing k R).toRingHom

noncomputable def envelopingRightModule : Module Rᵐᵒᵖ P :=
  Module.compHom P (Algebra.TensorProduct.includeRight : Rᵐᵒᵖ →ₐ[k] AlgebraEnvelopingRing k R).toRingHom

noncomputable def envelopingLeftScalarTower :
    letI := envelopingLeftModule k R P
    IsScalarTower k R P := by
  letI := envelopingLeftModule k R P
  constructor
  intro c r x
  change ((Algebra.TensorProduct.includeLeft : R →ₐ[k] AlgebraEnvelopingRing k R)
    (c • r)) • x=c • ((Algebra.TensorProduct.includeLeft : R →ₐ[k]
      AlgebraEnvelopingRing k R) r • x)
  rw [map_smul,smul_assoc]

noncomputable def envelopingRightScalarTower :
    letI := envelopingRightModule k R P
    IsScalarTower k Rᵐᵒᵖ P := by
  letI := envelopingRightModule k R P
  constructor
  intro c r x
  change ((Algebra.TensorProduct.includeRight : Rᵐᵒᵖ →ₐ[k] AlgebraEnvelopingRing k R)
    (c • r)) • x=c • ((Algebra.TensorProduct.includeRight : Rᵐᵒᵖ →ₐ[k]
      AlgebraEnvelopingRing k R) r • x)
  rw [map_smul,smul_assoc]

noncomputable def envelopingActionsCommute :
    letI := envelopingLeftModule k R P
    letI := envelopingRightModule k R P
    SMulCommClass R Rᵐᵒᵖ P := by
  letI := envelopingLeftModule k R P
  letI := envelopingRightModule k R P
  constructor
  intro a b x
  change (a ⊗ₜ[k] (1 : Rᵐᵒᵖ)) • ((1 : R) ⊗ₜ[k] b) • x=
    ((1 : R) ⊗ₜ[k] b) • (a ⊗ₜ[k] (1 : Rᵐᵒᵖ)) • x
  rw [← mul_smul,← mul_smul,Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul,mul_one,one_mul]

noncomputable def envelopingRightOperator (b : Rᵐᵒᵖ) :
    letI := envelopingLeftModule k R P
    letI := envelopingRightModule k R P
    P →ₗ[R] P := by
  letI := envelopingLeftModule k R P
  letI := envelopingRightModule k R P
  letI := envelopingActionsCommute k R P
  exact {
    toFun := fun x => b • x
    map_add' := smul_add b
    map_smul' := fun a x => (smul_comm a b x).symm}

variable {P} {P' : Type z} [AddCommGroup P'] [Module k P']
variable [Module (AlgebraEnvelopingRing k R) P'] [IsScalarTower k (AlgebraEnvelopingRing k R) P']

noncomputable def envelopingLeftLinearMap (f : P →ₗ[AlgebraEnvelopingRing k R] P') :
    letI := envelopingLeftModule k R P
    letI := envelopingLeftModule k R P'
    P →ₗ[R] P' := by
  letI := envelopingLeftModule k R P
  letI := envelopingLeftModule k R P'
  exact {
    toFun := f
    map_add' := f.map_add
    map_smul' := fun a x => f.map_smul
      ((Algebra.TensorProduct.includeLeft : R →ₐ[k] AlgebraEnvelopingRing k R) a) x}

omit [Module k P] [IsScalarTower k (AlgebraEnvelopingRing k R) P]
  [Module k P'] [IsScalarTower k (AlgebraEnvelopingRing k R) P'] in
theorem envelopingLinearMap_right_smul (f : P →ₗ[AlgebraEnvelopingRing k R] P')
    (b : Rᵐᵒᵖ) (x : P) :
    letI := envelopingRightModule k R P
    letI := envelopingRightModule k R P'
    f (b • x)=b • f x :=
  f.map_smul (Algebra.TensorProduct.includeRight b) x

end ASGinzburg
