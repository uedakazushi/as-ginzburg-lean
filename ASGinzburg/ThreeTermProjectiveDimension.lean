import ASGinzburg.FourTermProjectiveDimension
import ASGinzburg.FoundationSimpleProjectiveResolution

/-! Genuine projective resolutions with zero degree-three term bound
projective dimension by two. Apply this to the original AS foundation
restriction, without adding a global-dimension hypothesis. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

theorem threeTermProjectiveResolution_hasProjectiveDimensionLE {X : C}
    (P : ProjectiveResolution X) (h₃ : IsZero (P.complex.X 3))
    (h₄ : IsZero (P.complex.X 4)) : HasProjectiveDimensionLE X 2 := by
  haveI : IsIso P.secondCover := (P.shortExact₂ h₄).isIso_g_iff.mpr h₃
  haveI : Projective (kernel P.firstCover) :=
    Projective.of_iso (asIso P.secondCover) (by infer_instance)
  have h₁ : HasProjectiveDimensionLT (kernel (P.π.f 0)) 2 :=
    P.shortExact₁.hasProjectiveDimensionLT_X₃ 1 inferInstance
      (hasProjectiveDimensionLT_of_ge (P.complex.X 1) 1 2 (by decide))
  exact P.shortExact₀.hasProjectiveDimensionLT_X₃ 2 h₁
    (hasProjectiveDimensionLT_of_ge (P.complex.X 0) 1 3 (by decide))

end ASGinzburg

namespace ASGinzburg.ZAlgebra.ASResolution
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k} {Q : CutQuiver}
  {j : Q.Vertex} (R : A.ASResolution Q (j,0))

include R in
theorem foundation_simple_hasProjectiveDimensionLE_two :
    HasProjectiveDimensionLE
      ((A.foundationRestriction Q).obj (A.simpleRightModule (Q.height (j,0)))) 2 :=
  threeTermProjectiveResolution_hasProjectiveDimensionLE R.foundationProjectiveResolution
    R.foundationProjectiveResolution_X_three_isZero
    (R.foundationProjectiveResolution_X_ge_four_isZero 0)

end ASGinzburg.ZAlgebra.ASResolution
