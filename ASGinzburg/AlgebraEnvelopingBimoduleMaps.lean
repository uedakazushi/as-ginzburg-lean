import ASGinzburg.AlgebraEnvelopingRegularModule

/-! Maps of genuine k-linear bimodules are exactly maps linear over
the actual enveloping algebra. The tensor module action is mathlib's
commuting-action construction. -/
namespace ASGinzburg
open scoped TensorProduct
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M]
variable [Module R M] [Module Rᵐᵒᵖ M]
variable [IsScalarTower k R M] [IsScalarTower k Rᵐᵒᵖ M]
variable [SMulCommClass R Rᵐᵒᵖ M]

noncomputable def bimoduleEnvelopingModule : Module (AlgebraEnvelopingRing k R) M :=
  TensorProduct.Algebra.module

theorem bimoduleEnvelopingModule_tmul_smul (a : R) (b : Rᵐᵒᵖ) (x : M) :
    letI := bimoduleEnvelopingModule k R M
    (a ⊗ₜ[k] b) • x = a • b • x := by
  letI := bimoduleEnvelopingModule k R M
  rfl

theorem regularEnvelopingModule_eq_bimoduleEnvelopingModule :
    regularEnvelopingModule k R = bimoduleEnvelopingModule k R R := by
  apply Module.ext'
  intro t x
  letI := bimoduleEnvelopingModule k R R
  change regularEnvelopingRepresentation k R t x = t • x
  refine TensorProduct.inductionOn (motive := fun t =>
    regularEnvelopingRepresentation k R t x = t • x) t ?_ ?_
  · intro a b
    rw [bimoduleEnvelopingModule_tmul_smul]
    change regularEnvelopingRepresentation k R (a ⊗ₜ[k] MulOpposite.op b.unop) x =
      a * (x * b.unop)
    rw [regularEnvelopingRepresentation_tmul]
    exact mul_assoc a x b.unop
  · intro a b ha hb
    rw [map_add, LinearMap.add_apply, add_smul, ha, hb]

variable (N : Type z) [AddCommGroup N] [Module k N]
variable [Module R N] [Module Rᵐᵒᵖ N]
variable [IsScalarTower k R N] [IsScalarTower k Rᵐᵒᵖ N]
variable [SMulCommClass R Rᵐᵒᵖ N]

noncomputable def bimoduleEnvelopingLinearMap (f : M →ₗ[k] N)
    (hleft : ∀ (a : R) (x : M), f (a • x) = a • f x)
    (hright : ∀ (b : Rᵐᵒᵖ) (x : M), f (b • x) = b • f x) :
    letI := bimoduleEnvelopingModule k R M
    letI := bimoduleEnvelopingModule k R N
    M →ₗ[AlgebraEnvelopingRing k R] N := by
  letI := bimoduleEnvelopingModule k R M
  letI := bimoduleEnvelopingModule k R N
  exact
    { toFun := f
      map_add' := map_add f
      map_smul' := fun t x => by
        change f (t • x) = t • f x
        refine TensorProduct.inductionOn (motive := fun t => f (t • x) = t • f x)
          t ?_ ?_
        · intro a b
          change f (a • b • x) = a • b • f x
          rw [hleft, hright]
        · intro a b ha hb
          rw [add_smul, map_add, ha, hb, add_smul] }

theorem bimoduleEnvelopingLinearMap_apply (f : M →ₗ[k] N)
    (hleft : ∀ (a : R) (x : M), f (a • x) = a • f x)
    (hright : ∀ (b : Rᵐᵒᵖ) (x : M), f (b • x) = b • f x) (x : M) :
    bimoduleEnvelopingLinearMap k R M N f hleft hright x = f x := rfl

theorem bimoduleEnvelopingLinearMap_smul_iff (f : M →ₗ[k] N) :
    letI := bimoduleEnvelopingModule k R M
    letI := bimoduleEnvelopingModule k R N
    (∀ (t : AlgebraEnvelopingRing k R) (x : M), f (t • x) = t • f x) ↔
      (∀ (a : R) (x : M), f (a • x) = a • f x) ∧
      (∀ (b : Rᵐᵒᵖ) (x : M), f (b • x) = b • f x) := by
  letI := bimoduleEnvelopingModule k R M
  letI := bimoduleEnvelopingModule k R N
  constructor
  · intro h
    constructor
    · intro a x
      have ht := h (a ⊗ₜ[k] (1 : Rᵐᵒᵖ)) x
      change f (a • (1 : Rᵐᵒᵖ) • x) = a • (1 : Rᵐᵒᵖ) • f x at ht
      simpa only [one_smul] using ht
    · intro b x
      have ht := h ((1 : R) ⊗ₜ[k] b) x
      change f ((1 : R) • b • x) = (1 : R) • b • f x at ht
      simpa only [one_smul] using ht
  · rintro ⟨hleft, hright⟩ t x
    exact (bimoduleEnvelopingLinearMap k R M N f hleft hright).map_smul t x

end ASGinzburg
