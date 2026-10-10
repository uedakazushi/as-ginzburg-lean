import ASGinzburg.FourTermProjectiveResolution
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.CategoryTheory.Abelian.LeftDerived

/-! An actual projective-dimension bound produces a genuine finite
resolution, and therefore vanishing for every additive left-derived
functor. The bound is not a substitute for a resolution hypothesis. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] {X : C}

noncomputable def projectiveDimensionThreeResolution (P : ProjectiveResolution X)
    (hX : HasProjectiveDimensionLE X 3) : ProjectiveResolution X := by
  have h₁ : HasProjectiveDimensionLT (kernel (P.π.f 0)) 3 :=
    P.shortExact₀.hasProjectiveDimensionLT_X₁ 3 inferInstance hX
  have h₂ : HasProjectiveDimensionLT (kernel P.firstCover) 2 :=
    P.shortExact₁.hasProjectiveDimensionLT_X₁ 2 inferInstance h₁
  have h₃ : HasProjectiveDimensionLT (kernel P.secondCover) 1 :=
    (ShortComplex.ShortExact.mk (ShortComplex.exact_kernel P.secondCover)).hasProjectiveDimensionLT_X₁
      1 inferInstance h₂
  letI : Projective (kernel P.secondCover) :=
    (projective_iff_hasProjectiveDimensionLT_one _).mpr h₃
  exact (FourTermProjectiveResolution.ofKernelCovers
    (P.π.f 0) P.firstCover P.secondCover).toProjectiveResolution

theorem projectiveDimensionThreeResolution_isZero_ge_four
    (P : ProjectiveResolution X) (hX : HasProjectiveDimensionLE X 3) (n : ℕ) :
    IsZero ((projectiveDimensionThreeResolution P hX).complex.X (n+4)) := by
  change IsZero (0 : C)
  exact isZero_zero C

variable [HasProjectiveResolutions C] {D : Type*} [Category D] [Abelian D]

theorem leftDerived_isZero_of_projectiveDimensionLE_three
    (F : C ⥤ D) [F.Additive] (hX : HasProjectiveDimensionLE X 3) (n : ℕ) :
    IsZero ((F.leftDerived (n+4)).obj X) := by
  let P := projectiveDimensionThreeResolution (projectiveResolution X) hX
  let K := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  have hK : IsZero (K.homology (n+4)) :=
    (K.sc (n+4)).isZero_homology_of_isZero_X₂
      (F.map_isZero (projectiveDimensionThreeResolution_isZero_ge_four
        (projectiveResolution X) hX n))
  exact IsZero.of_iso hK (P.isoLeftDerivedObj F (n+4))

end ASGinzburg
