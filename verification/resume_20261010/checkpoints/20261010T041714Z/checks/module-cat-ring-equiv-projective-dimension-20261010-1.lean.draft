import ASGinzburg.ProjectiveDimensionThreeDerivedVanishing
import ASGinzburg.FourTermProjectiveDimension
import ASGinzburg.ModuleCatRestrictionHomology
import Mathlib.Algebra.Category.ModuleCat.Projective

/-! An actual finite projective resolution transports a projective-dimension
bound through restriction by a ring equivalence. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
universe u v z
variable {R : Type u} [Ring R] {S : Type v} [Ring S]

theorem moduleCatRingEquiv_hasProjectiveDimensionLE_three
    [Small.{z} S] (e : R ≃+* S) (X : ModuleCat.{z} S)
    (hX : HasProjectiveDimensionLE X 3) :
    HasProjectiveDimensionLE ((ModuleCat.restrictScalars e.toRingHom).obj X) 3 := by
  let F := ModuleCat.restrictScalars.{z} e.toRingHom
  letI := moduleCatRestrictionPreservesHomology.{u,v,z} e.toRingHom
  let P := projectiveDimensionThreeResolution (projectiveResolution X) hX
  exact fourTermProjectiveResolution_hasProjectiveDimensionLE
    (F.mapProjectiveResolution P)
    (F.map_isZero (projectiveDimensionThreeResolution_isZero_ge_four
      (projectiveResolution X) hX 0))

end ASGinzburg
