import ASGinzburg.ProjectiveResolutionSyzygies
import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-! Actual four-term projective resolutions bound projective dimension
in any abelian category, by the three actual syzygy short exact sequences. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

theorem fourTermProjectiveResolution_hasProjectiveDimensionLE {X : C}
    (P : ProjectiveResolution X) (h₄ : IsZero (P.complex.X 4)) :
    HasProjectiveDimensionLE X 3 := by
  have h₂ : HasProjectiveDimensionLT (kernel P.firstCover) 2 :=
    (P.shortExact₂ h₄).hasProjectiveDimensionLT_X₃ 1 inferInstance
      (hasProjectiveDimensionLT_of_ge (P.complex.X 2) 1 2 (by decide))
  have h₁ : HasProjectiveDimensionLT (kernel (P.π.f 0)) 3 :=
    P.shortExact₁.hasProjectiveDimensionLT_X₃ 2 h₂
      (hasProjectiveDimensionLT_of_ge (P.complex.X 1) 1 3 (by decide))
  exact P.shortExact₀.hasProjectiveDimensionLT_X₃ 3 h₁
    (hasProjectiveDimensionLT_of_ge (P.complex.X 0) 1 4 (by decide))

end ASGinzburg
