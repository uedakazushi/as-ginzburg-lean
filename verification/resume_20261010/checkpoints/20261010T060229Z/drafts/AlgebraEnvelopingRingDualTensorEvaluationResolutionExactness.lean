import work.ASGinzburgDraft.OrdinaryRightRingHomFieldComplexExactness
import ASGinzburg.EnvelopingBalancedTensorResolution
import ASGinzburg.EnvelopingBalancedTensorRegularUnit
import ASGinzburg.ProjectiveResolutionChangeTarget

/-! Genuine enveloping resolutions become right-module resolutions
of M through the actual balanced tensor unit. Actual derived Ext
vanishing then supplies exactness of the vector Hom target complex. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ModuleCat.Algebra
universe u v
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : ModuleCat.{v} Rᵐᵒᵖ)
variable (Q : ProjectiveResolution (regularEnvelopingModuleCat k R))

noncomputable def envelopingBalancedTensorRegularProjectiveResolution :
    ProjectiveResolution M :=
  projectiveResolutionChangeTarget (envelopingBalancedTensorProjectiveResolution k R M Q)
    (envelopingBalancedTensorRegularRightEquiv k R M).toModuleIso

theorem envelopingBalancedTensorRegularProjectiveResolution_term_four_isZero
    (h₄ : IsZero (Q.complex.X 4)) :
    IsZero ((envelopingBalancedTensorRegularProjectiveResolution k R M Q).complex.X 4) := by
  change IsZero ((envelopingBalancedTensorRightFunctor k R M).obj (Q.complex.X 4))
  exact (envelopingBalancedTensorRightFunctor k R M).map_isZero h₄

theorem envelopingRingDualTensorEvaluationTarget_exactAt_low_of_ext_zero
    (h₄ : IsZero (Q.complex.X 4))
    (hExt : ∀ n, n<3 → ∀ e : Abelian.Ext.{v} M (ModuleCat.of Rᵐᵒᵖ R) n, e=0)
    (n : ℕ) (hn : n<3) :
    (((envelopingRingDualTensorEvaluationTargetFunctor k R M).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj Q.complex.op).ExactAt n := by
  change (ordinaryRightRingHomFieldComplex k R
    (envelopingBalancedTensorRegularProjectiveResolution k R M Q)).ExactAt n
  exact ordinaryRightRingHomFieldComplex_exactAt_low_of_ext_zero k R _
    (envelopingBalancedTensorRegularProjectiveResolution_term_four_isZero k R M Q h₄)
    hExt n hn

end ASGinzburg
