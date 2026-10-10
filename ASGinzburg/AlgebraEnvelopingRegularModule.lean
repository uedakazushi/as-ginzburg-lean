import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Algebra.Category.ModuleCat.Basic

/-! The actual enveloping algebra R tensor R-op acts on R by left and
right multiplication. The action is an actual algebra representation. -/
namespace ASGinzburg
open scoped TensorProduct
universe u v
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]

abbrev AlgebraEnvelopingRing := R ⊗[k] Rᵐᵒᵖ

noncomputable def regularRightAlgebraRepresentation : Rᵐᵒᵖ →ₐ[k] Module.End k R where
  toFun b := LinearMap.mulRight k b.unop
  map_zero' := by
    apply LinearMap.ext
    intro x
    exact mul_zero x
  map_one' := by
    apply LinearMap.ext
    intro x
    exact mul_one x
  map_add' b c := by
    apply LinearMap.ext
    intro x
    exact mul_add x b.unop c.unop
  map_mul' b c := by
    apply LinearMap.ext
    intro x
    exact (mul_assoc x c.unop b.unop).symm
  commutes' c := by
    apply LinearMap.ext
    intro x
    change x*algebraMap k R c=c • x
    rw [Algebra.smul_def]
    exact (Algebra.commutes c x).symm

noncomputable def regularEnvelopingRepresentation : AlgebraEnvelopingRing k R →ₐ[k] Module.End k R :=
  Algebra.TensorProduct.lift (Algebra.lsmul k k R) (regularRightAlgebraRepresentation k R)
    (fun a b => by
      apply LinearMap.ext
      intro x
      exact (mul_assoc a x b.unop).symm)

theorem regularEnvelopingRepresentation_tmul (a b x : R) :
    regularEnvelopingRepresentation k R (a ⊗ₜ[k] MulOpposite.op b) x=a*x*b := by
  rw [regularEnvelopingRepresentation,Algebra.TensorProduct.lift_tmul]
  exact (mul_assoc a x b).symm

noncomputable def regularEnvelopingModule : Module (AlgebraEnvelopingRing k R) R :=
  Module.compHom R (regularEnvelopingRepresentation k R).toRingHom

noncomputable def regularEnvelopingModuleCat : ModuleCat (AlgebraEnvelopingRing k R) := by
  letI := regularEnvelopingModule k R
  exact ModuleCat.of _ R

theorem regularEnvelopingModule_tmul_smul (a b x : R) :
    letI := regularEnvelopingModule k R
    (a ⊗ₜ[k] MulOpposite.op b) • x=a*x*b := by
  letI := regularEnvelopingModule k R
  exact regularEnvelopingRepresentation_tmul k R a b x

end ASGinzburg
