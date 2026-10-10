import ASGinzburg.AlgebraEnvelopingScalars

/-! The actual multiplication bimodule is cyclic over the enveloping
algebra, even when the underlying k-vector space is infinite dimensional. -/
namespace ASGinzburg
open scoped TensorProduct
universe u v
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]

noncomputable def regularEnvelopingGeneratorMap :
    letI := regularEnvelopingModule k R
    AlgebraEnvelopingRing k R →ₗ[AlgebraEnvelopingRing k R] R := by
  letI := regularEnvelopingModule k R
  exact LinearMap.id.smulRight (1 : R)

theorem regularEnvelopingGeneratorMap_surjective :
    Function.Surjective (regularEnvelopingGeneratorMap k R) := by
  intro r
  refine ⟨r ⊗ₜ[k] (1 : Rᵐᵒᵖ), ?_⟩
  change regularEnvelopingRepresentation k R (r ⊗ₜ[k] MulOpposite.op 1) 1 = r
  rw [regularEnvelopingRepresentation_tmul, mul_one, mul_one]

theorem regularEnvelopingModule_finite_of_cyclic :
    letI := regularEnvelopingModule k R
    Module.Finite (AlgebraEnvelopingRing k R) R := by
  letI := regularEnvelopingModule k R
  exact Module.Finite.of_surjective (regularEnvelopingGeneratorMap k R)
    (regularEnvelopingGeneratorMap_surjective k R)

end ASGinzburg
