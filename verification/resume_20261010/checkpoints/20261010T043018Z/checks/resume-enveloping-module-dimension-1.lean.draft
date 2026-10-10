import work.ASGinzburgDraft.EnvelopingResolutionRightProjectiveDimension
import work.ASGinzburgDraft.ProjectiveDimensionThreeDerivedVanishing

/-! An actual projective-dimension bound for the multiplication bimodule
produces actual finite resolutions for every ordinary right module. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u v
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]

theorem rightModule_hasProjectiveDimensionLE_three_of_enveloping_dimension
    (M : ModuleCat.{v} Rᵐᵒᵖ)
    (hR : HasProjectiveDimensionLE (regularEnvelopingModuleCat k R) 3) :
    HasProjectiveDimensionLE M 3 := by
  let P := projectiveDimensionThreeResolution
    (projectiveResolution (regularEnvelopingModuleCat k R)) hR
  exact rightModule_hasProjectiveDimensionLE_three_of_enveloping_resolution k R M P
    (projectiveDimensionThreeResolution_isZero_ge_four
      (projectiveResolution (regularEnvelopingModuleCat k R)) hR 0)

end ASGinzburg
