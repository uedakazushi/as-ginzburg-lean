import ASGinzburg.FoundationRingEquivalenceLinear
import ASGinzburg.FoundationExtBounds

/-! The original AS-restricted projective resolution becomes a real
projective resolution over the finite foundation ring. Its actual
zero third term gives projective dimension at most two. -/
namespace ASGinzburg.ZAlgebra.ASResolution
open CategoryTheory CategoryTheory.Limits
universe u
variable {k : Type u} [Field k] {A : ZAlgebra.{u,u} k} {Q : CutQuiver}
  {j : Q.Vertex} (R : A.ASResolution Q (j,0))

noncomputable def foundationRingProjectiveResolution :
    ProjectiveResolution (A.foundationRightTotalModule Q
      ((A.foundationRestriction Q).obj (A.simpleRightModule (Q.height (j,0))))) :=
  (A.foundationRightTotalFunctor Q).mapProjectiveResolution R.foundationProjectiveResolution

theorem foundationRingProjectiveResolution_X_three_isZero :
    IsZero (R.foundationRingProjectiveResolution.complex.X 3) := by
  exact (A.foundationRightTotalFunctor Q).map_isZero R.foundationProjectiveResolution_X_three_isZero

theorem foundationRingProjectiveResolution_X_ge_four_isZero (n : ℕ) :
    IsZero (R.foundationRingProjectiveResolution.complex.X (n+4)) := by
  exact (A.foundationRightTotalFunctor Q).map_isZero (R.foundationProjectiveResolution_X_ge_four_isZero n)

include R in
theorem foundation_ring_simple_hasProjectiveDimensionLE_two :
    HasProjectiveDimensionLE (A.foundationRightTotalModule Q
      ((A.foundationRestriction Q).obj (A.simpleRightModule (Q.height (j,0))))) 2 :=
  ASGinzburg.threeTermProjectiveResolution_hasProjectiveDimensionLE
    R.foundationRingProjectiveResolution R.foundationRingProjectiveResolution_X_three_isZero
    (R.foundationRingProjectiveResolution_X_ge_four_isZero 0)

end ASGinzburg.ZAlgebra.ASResolution
