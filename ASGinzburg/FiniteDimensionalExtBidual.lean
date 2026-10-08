import ASGinzburg.RightResolutionExtBidual
import ASGinzburg.LeftResolutionExtBidual
import ASGinzburg.ASFiniteDimensionalProjectiveResolution
import ASGinzburg.FiniteDimensionalExtConcentration

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

/-- Object comparison; functorial naturality is a separate obligation. -/
noncomputable def rightFiniteDimensionalExtBidualIso (hAS : A.ASRegular Q)
    (M : A.RightModule) (hM : A.rightFiniteDimensionalProperty M) :
    A.leftModuleExtRight (A.rightModuleExtLeft M 3) 3 ≅ M :=
  A.rightResolutionExtBidualIso (A.rightFiniteDimensionalProjectiveResolution Q hAS M hM)
    (A.rightFiniteDimensionalProjectiveResolution_isZero_ge_four Q hAS M hM 0)
    (fun n _ => A.rightFiniteDimensionalProjectiveResolution_finite Q hAS M hM n)
    (fun i n hn e => A.rightFiniteDimensional_ext_other_eq_zero Q hAS M hM i n
      (by omega) e)

/-- The left object comparison follows from the original right AS conditions. -/
noncomputable def leftFiniteDimensionalExtBidualIso (hAS : A.ASRegular Q)
    (M : A.LeftModule) (hM : A.leftFiniteDimensionalProperty M) :
    A.rightModuleExtLeft (A.leftModuleExtRight M 3) 3 ≅ M :=
  A.leftResolutionExtBidualIso (A.leftFiniteDimensionalProjectiveResolution Q hAS M hM)
    (A.leftFiniteDimensionalProjectiveResolution_isZero_ge_four Q hAS M hM 0)
    (fun n _ => A.leftFiniteDimensionalProjectiveResolution_finite Q hAS M hM n)
    (fun i n hn e => A.leftFiniteDimensional_ext_other_eq_zero Q hAS M hM i n
      (by omega) e)
end ASGinzburg.ZAlgebra
