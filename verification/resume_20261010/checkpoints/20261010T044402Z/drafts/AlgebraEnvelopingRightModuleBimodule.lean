import ASGinzburg.AlgebraEnvelopingRegularModule
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import work.ASGinzburgDraft.OrdinaryModuleRingDual

/-! Actual right enveloping modules are actual bimodules: the left R
action comes from the second tensor factor, and the right R action from
the first. Ring-Hom duals inherit these actions by multiplication in
their actual value ring. -/
namespace ASGinzburg
open scoped TensorProduct
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]

noncomputable def rightEnvelopingLeftRingHom :
    R →+* (AlgebraEnvelopingRing k R)ᵐᵒᵖ :=
  (Algebra.TensorProduct.includeRight : Rᵐᵒᵖ →ₐ[k]
    AlgebraEnvelopingRing k R).toRingHom.op.comp (RingEquiv.opOp R).toRingHom

noncomputable def rightEnvelopingRightRingHom :
    Rᵐᵒᵖ →+* (AlgebraEnvelopingRing k R)ᵐᵒᵖ :=
  (Algebra.TensorProduct.includeLeft : R →ₐ[k]
    AlgebraEnvelopingRing k R).toRingHom.op

variable (P : Type w) [AddCommGroup P] [Module (AlgebraEnvelopingRing k R)ᵐᵒᵖ P]

noncomputable def rightEnvelopingLeftModule : Module R P :=
  Module.compHom P (rightEnvelopingLeftRingHom k R)

noncomputable def rightEnvelopingRightModule : Module Rᵐᵒᵖ P :=
  Module.compHom P (rightEnvelopingRightRingHom k R)

noncomputable def rightEnvelopingActionsCommute :
    letI := rightEnvelopingLeftModule k R P
    letI := rightEnvelopingRightModule k R P
    SMulCommClass R Rᵐᵒᵖ P := by
  letI := rightEnvelopingLeftModule k R P
  letI := rightEnvelopingRightModule k R P
  constructor
  intro a b x
  change MulOpposite.op ((1 : R) ⊗ₜ[k] MulOpposite.op a) •
      (MulOpposite.op (b.unop ⊗ₜ[k] (1 : Rᵐᵒᵖ)) • x) =
    MulOpposite.op (b.unop ⊗ₜ[k] (1 : Rᵐᵒᵖ)) •
      (MulOpposite.op ((1 : R) ⊗ₜ[k] MulOpposite.op a) • x)
  rw [← mul_smul, ← mul_smul, ← MulOpposite.op_mul, ← MulOpposite.op_mul,
    Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul, mul_one, one_mul]

theorem rightEnvelopingModule_tmul_smul (a b : R) (x : P) :
    letI := rightEnvelopingLeftModule k R P
    letI := rightEnvelopingRightModule k R P
    MulOpposite.op (a ⊗ₜ[k] MulOpposite.op b) • x = b • (MulOpposite.op a • x) := by
  letI := rightEnvelopingLeftModule k R P
  letI := rightEnvelopingRightModule k R P
  change MulOpposite.op (a ⊗ₜ[k] MulOpposite.op b) • x =
    MulOpposite.op ((1 : R) ⊗ₜ[k] MulOpposite.op b) •
      (MulOpposite.op (a ⊗ₜ[k] (1 : Rᵐᵒᵖ)) • x)
  rw [← mul_smul, ← MulOpposite.op_mul, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul]

noncomputable def rightEnvelopingLeftRestrictionFunctor :
    ModuleCat.{w} (AlgebraEnvelopingRing k R)ᵐᵒᵖ ⥤ ModuleCat.{w} R :=
  ModuleCat.restrictScalars (rightEnvelopingLeftRingHom k R)

noncomputable def rightEnvelopingRightRestrictionFunctor :
    ModuleCat.{w} (AlgebraEnvelopingRing k R)ᵐᵒᵖ ⥤ ModuleCat.{w} Rᵐᵒᵖ :=
  ModuleCat.restrictScalars (rightEnvelopingRightRingHom k R)

variable {P} {P' : Type z} [AddCommGroup P']
  [Module (AlgebraEnvelopingRing k R)ᵐᵒᵖ P']

noncomputable def rightEnvelopingLeftLinearMap
    (f : P →ₗ[(AlgebraEnvelopingRing k R)ᵐᵒᵖ] P') :
    letI := rightEnvelopingLeftModule k R P
    letI := rightEnvelopingLeftModule k R P'
    P →ₗ[R] P' := by
  letI := rightEnvelopingLeftModule k R P
  letI := rightEnvelopingLeftModule k R P'
  exact {
    toFun := f
    map_add' := f.map_add
    map_smul' := fun a x => f.map_smul (rightEnvelopingLeftRingHom k R a) x }

theorem rightEnvelopingLinearMap_right_smul
    (f : P →ₗ[(AlgebraEnvelopingRing k R)ᵐᵒᵖ] P') (b : Rᵐᵒᵖ) (x : P) :
    letI := rightEnvelopingRightModule k R P
    letI := rightEnvelopingRightModule k R P'
    f (b • x) = b • f x :=
  f.map_smul (rightEnvelopingRightRingHom k R b) x

variable (M : ModuleCat.{v} (AlgebraEnvelopingRing k R))

theorem rightEnvelopingRingDual_left_smul_apply (b : R)
    (f : ordinaryRingDual (AlgebraEnvelopingRing k R) M) (x : M) :
    letI := rightEnvelopingLeftModule k R (ordinaryRingDual (AlgebraEnvelopingRing k R) M)
    (b • f) x = f x * ((1 : R) ⊗ₜ[k] MulOpposite.op b) := rfl

theorem rightEnvelopingRingDual_right_smul_apply (a : R)
    (f : ordinaryRingDual (AlgebraEnvelopingRing k R) M) (x : M) :
    letI := rightEnvelopingRightModule k R (ordinaryRingDual (AlgebraEnvelopingRing k R) M)
    (MulOpposite.op a • f) x = f x * (a ⊗ₜ[k] (1 : Rᵐᵒᵖ)) := rfl

end ASGinzburg
