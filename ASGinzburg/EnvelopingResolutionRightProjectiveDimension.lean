import ASGinzburg.EnvelopingBalancedTensorResolution
import ASGinzburg.EnvelopingBalancedTensorRegularUnit
import ASGinzburg.FourTermProjectiveDimension

/-! A genuine four-term projective resolution of the multiplication
bimodule R bounds the actual projective dimension of every right R
module by three. No tensor exactness or global-dimension hypothesis is
assumed: the tensor resolution and its unit are constructed above. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u v
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]

noncomputable def envelopingBalancedTensorRegularModuleIso (M : ModuleCat.{v} Rᵐᵒᵖ) :
    (envelopingBalancedTensorRightFunctor.{u,v,v,v} k R M).obj
      (regularEnvelopingModuleCat k R) ≅ M := by
  letI := envelopingBalancedTensorRightModule k R M (regularEnvelopingModuleCat k R)
  exact (envelopingBalancedTensorRegularRightEquiv k R M).toModuleIso

noncomputable def envelopingResolutionRightProjectiveResolution
    (M : ModuleCat.{v} Rᵐᵒᵖ) (Q : ProjectiveResolution (regularEnvelopingModuleCat k R)) :
    ProjectiveResolution M where
  complex := (envelopingBalancedTensorProjectiveResolution k R M Q).complex
  projective := (envelopingBalancedTensorProjectiveResolution k R M Q).projective
  π := (envelopingBalancedTensorProjectiveResolution k R M Q).π ≫
    (ChainComplex.single₀ _).map (envelopingBalancedTensorRegularModuleIso k R M).hom
  quasiIso := by
    infer_instance

theorem envelopingResolutionRightProjectiveResolution_isZero
    (M : ModuleCat.{v} Rᵐᵒᵖ) (Q : ProjectiveResolution (regularEnvelopingModuleCat k R))
    (n : ℕ) (hn : IsZero (Q.complex.X n)) :
    IsZero ((envelopingResolutionRightProjectiveResolution k R M Q).complex.X n) :=
  (envelopingBalancedTensorRightFunctor.{u,v,v,v} k R M).map_isZero hn

theorem rightModule_hasProjectiveDimensionLE_three_of_enveloping_resolution
    (M : ModuleCat.{v} Rᵐᵒᵖ) (Q : ProjectiveResolution (regularEnvelopingModuleCat k R))
    (h₄ : IsZero (Q.complex.X 4)) : HasProjectiveDimensionLE M 3 :=
  fourTermProjectiveResolution_hasProjectiveDimensionLE
    (envelopingResolutionRightProjectiveResolution k R M Q)
    (envelopingResolutionRightProjectiveResolution_isZero k R M Q 4 h₄)

end ASGinzburg
