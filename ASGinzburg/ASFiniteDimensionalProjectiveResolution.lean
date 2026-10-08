import ASGinzburg.FiniteProjectiveFourTermResolution
import ASGinzburg.ASFiniteDimensionalResolutionLength

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

/-- A genuine four-term projective resolution, derived from the original AS conditions. -/
noncomputable def rightFiniteDimensionalProjectiveResolution (hAS : A.ASRegular Q)
    (M : A.RightModule) (hM : A.rightFiniteDimensionalProperty M) : ProjectiveResolution M :=
  A.rightFiniteProjectiveProjectiveResolution M
    (A.rightFiniteDimensional_hasFiniteProjectiveResolutionLength Q hAS M hM)

theorem rightFiniteDimensionalProjectiveResolution_finite (hAS : A.ASRegular Q)
    (M : A.RightModule) (hM : A.rightFiniteDimensionalProperty M) (n : ℕ) :
    A.rightFiniteProjectiveProperty ((A.rightFiniteDimensionalProjectiveResolution Q hAS M hM).complex.X n) :=
  A.rightFiniteProjectiveProjectiveResolution_finite M
    (A.rightFiniteDimensional_hasFiniteProjectiveResolutionLength Q hAS M hM) n

theorem rightFiniteDimensionalProjectiveResolution_isZero_ge_four (hAS : A.ASRegular Q)
    (M : A.RightModule) (hM : A.rightFiniteDimensionalProperty M) (n : ℕ) :
    IsZero ((A.rightFiniteDimensionalProjectiveResolution Q hAS M hM).complex.X (n+4)) :=
  A.rightFiniteProjectiveProjectiveResolution_isZero_ge_four M
    (A.rightFiniteDimensional_hasFiniteProjectiveResolutionLength Q hAS M hM) n

/-- A genuine four-term left projective resolution, without an additional left AS axiom. -/
noncomputable def leftFiniteDimensionalProjectiveResolution (hAS : A.ASRegular Q)
    (M : A.LeftModule) (hM : A.leftFiniteDimensionalProperty M) : ProjectiveResolution M :=
  A.leftFiniteProjectiveProjectiveResolution M
    (A.leftFiniteDimensional_hasFiniteProjectiveResolutionLength Q hAS M hM)

theorem leftFiniteDimensionalProjectiveResolution_finite (hAS : A.ASRegular Q)
    (M : A.LeftModule) (hM : A.leftFiniteDimensionalProperty M) (n : ℕ) :
    A.leftFiniteProjectiveProperty ((A.leftFiniteDimensionalProjectiveResolution Q hAS M hM).complex.X n) :=
  A.leftFiniteProjectiveProjectiveResolution_finite M
    (A.leftFiniteDimensional_hasFiniteProjectiveResolutionLength Q hAS M hM) n

theorem leftFiniteDimensionalProjectiveResolution_isZero_ge_four (hAS : A.ASRegular Q)
    (M : A.LeftModule) (hM : A.leftFiniteDimensionalProperty M) (n : ℕ) :
    IsZero ((A.leftFiniteDimensionalProjectiveResolution Q hAS M hM).complex.X (n+4)) :=
  A.leftFiniteProjectiveProjectiveResolution_isZero_ge_four M
    (A.leftFiniteDimensional_hasFiniteProjectiveResolutionLength Q hAS M hM) n
end ASGinzburg.ZAlgebra
