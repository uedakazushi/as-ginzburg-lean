import work.ASGinzburgDraft.AlgebraEnvelopingTensorProjective
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! Finitely generated ordinary factors tensor to a finitely generated
right enveloping module. Finite free presentations provide the actual
surjection; projectivity is not assumed for this finite-generation result. -/
namespace ASGinzburg
open scoped TensorProduct
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module Rᵐᵒᵖ M]
variable (N : Type z) [AddCommGroup N] [Module k N] [Module R N]
variable [IsScalarTower k Rᵐᵒᵖ M] [IsScalarTower k R N]

attribute [local instance] tensorRightEnvelopingModule
attribute [local instance 2000] Semiring.toModule

theorem tensorRightEnvelopingModule_finite
    [Module.Finite Rᵐᵒᵖ M] [Module.Finite R N] :
    Module.Finite (AlgebraEnvelopingRing k R)ᵐᵒᵖ (M ⊗[k] N) := by
  obtain ⟨a, fM, hfM⟩ := Module.Finite.exists_fin' Rᵐᵒᵖ M
  obtain ⟨b, fN, hfN⟩ := Module.Finite.exists_fin' R N
  let eM : (Fin a →₀ R) ≃ₗ[Rᵐᵒᵖ] (Fin a → Rᵐᵒᵖ) :=
    (Finsupp.mapRange.linearEquiv (rightRegularUnopLinearEquiv R)).symm.trans
      (Finsupp.linearEquivFunOnFinite Rᵐᵒᵖ Rᵐᵒᵖ (Fin a))
  let eN : (Fin b →₀ R) ≃ₗ[R] (Fin b → R) :=
    Finsupp.linearEquivFunOnFinite R R (Fin b)
  let pM : (Fin a →₀ R) →ₗ[Rᵐᵒᵖ] M := fM.comp eM.toLinearMap
  let pN : (Fin b →₀ R) →ₗ[R] N := fN.comp eN.toLinearMap
  have hpM : Function.Surjective pM := hfM.comp eM.surjective
  have hpN : Function.Surjective pN := hfN.comp eN.surjective
  letI : Module.Finite (AlgebraEnvelopingRing k R)ᵐᵒᵖ
      ((Fin a →₀ R) ⊗[k] (Fin b →₀ R)) :=
    Module.Finite.equiv (tensorRightEnvelopingFinsuppEquiv k R (Fin a) (Fin b)).symm
  apply Module.Finite.of_surjective (tensorRightEnvelopingMap k R pM pN)
  change Function.Surjective (TensorProduct.map (pM.restrictScalars k) (pN.restrictScalars k))
  exact TensorProduct.map_surjective hpM hpN

end ASGinzburg
