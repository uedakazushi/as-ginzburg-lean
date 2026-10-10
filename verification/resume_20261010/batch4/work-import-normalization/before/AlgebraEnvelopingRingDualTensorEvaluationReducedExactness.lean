import work.ASGinzburgDraft.AlgebraEnvelopingRingDualTensorEvaluationComplexNaturality
import work.ASGinzburgDraft.AlgebraEnvelopingRingDualTensorEvaluationResolutionExactness

/-! For a genuine finite-projective enveloping resolution, actual
ordinary Ext vanishing implies low exactness after right tensor
reduction of its genuine ring dual. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ModuleCat.Algebra
universe u v
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : ModuleCat.{v} Rᵐᵒᵖ) [Module.Finite k M]
variable (Q : ProjectiveResolution (regularEnvelopingModuleCat k R))

theorem envelopingRingDualTensorEvaluationSource_exactAt_low_of_ext_zero
    (hQ : ∀ i, ordinaryFiniteProjectiveProperty (AlgebraEnvelopingRing k R) (Q.complex.X i))
    (h₄ : IsZero (Q.complex.X 4))
    (hExt : ∀ n, n<3 → ∀ e : Abelian.Ext.{v} M (ModuleCat.of Rᵐᵒᵖ R) n, e=0)
    (n : ℕ) (hn : n<3) :
    (((envelopingRingDualTensorEvaluationSourceFunctor k R M).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj Q.complex.op).ExactAt n := by
  let e := envelopingFiniteProjectiveRingDualTensorComplexIso k R M Q.complex hQ
  exact (HomologicalComplex.exactAt_iff_of_quasiIsoAt e.hom n).mpr
    (envelopingRingDualTensorEvaluationTarget_exactAt_low_of_ext_zero k R M Q h₄ hExt n hn)

end ASGinzburg
