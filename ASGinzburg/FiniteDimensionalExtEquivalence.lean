import ASGinzburg.ResolutionExtBidualNaturality
import ASGinzburg.FiniteDimensionalExtBidual
import ASGinzburg.FiniteDimensionalExtDuality

namespace ASGinzburg.ZAlgebra
open CategoryTheory Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem rightFiniteDimensionalExtBidualIso_natural (hAS : A.ASRegular Q)
    (M N : A.RightModule) (hM : A.rightFiniteDimensionalProperty M)
    (hN : A.rightFiniteDimensionalProperty N) (f : M ⟶ N) :
    A.leftModuleExtPrecompRight (A.rightModuleExtPrecompLeft f 3) 3 ≫
      (A.rightFiniteDimensionalExtBidualIso Q hAS N hN).hom =
    (A.rightFiniteDimensionalExtBidualIso Q hAS M hM).hom ≫ f := by
  let PM := A.rightFiniteDimensionalProjectiveResolution Q hAS M hM
  let PN := A.rightFiniteDimensionalProjectiveResolution Q hAS N hN
  exact A.rightResolutionExtBidualIso_natural PM PN
    (A.rightFiniteDimensionalProjectiveResolution_isZero_ge_four Q hAS M hM 0)
    (A.rightFiniteDimensionalProjectiveResolution_isZero_ge_four Q hAS N hN 0)
    (fun n _ => A.rightFiniteDimensionalProjectiveResolution_finite Q hAS M hM n)
    (fun n _ => A.rightFiniteDimensionalProjectiveResolution_finite Q hAS N hN n)
    (fun i n hn e => A.rightFiniteDimensional_ext_other_eq_zero Q hAS M hM i n (by omega) e)
    (fun i n hn e => A.rightFiniteDimensional_ext_other_eq_zero Q hAS N hN i n (by omega) e)
    (ProjectiveResolution.lift f PM PN) f (ProjectiveResolution.lift_commutes_zero f PM PN)

theorem leftFiniteDimensionalExtBidualIso_natural (hAS : A.ASRegular Q)
    (M N : A.LeftModule) (hM : A.leftFiniteDimensionalProperty M)
    (hN : A.leftFiniteDimensionalProperty N) (f : M ⟶ N) :
    A.rightModuleExtPrecompLeft (A.leftModuleExtPrecompRight f 3) 3 ≫
      (A.leftFiniteDimensionalExtBidualIso Q hAS N hN).hom =
    (A.leftFiniteDimensionalExtBidualIso Q hAS M hM).hom ≫ f := by
  let PM := A.leftFiniteDimensionalProjectiveResolution Q hAS M hM
  let PN := A.leftFiniteDimensionalProjectiveResolution Q hAS N hN
  exact A.leftResolutionExtBidualIso_natural PM PN
    (A.leftFiniteDimensionalProjectiveResolution_isZero_ge_four Q hAS M hM 0)
    (A.leftFiniteDimensionalProjectiveResolution_isZero_ge_four Q hAS N hN 0)
    (fun n _ => A.leftFiniteDimensionalProjectiveResolution_finite Q hAS M hM n)
    (fun n _ => A.leftFiniteDimensionalProjectiveResolution_finite Q hAS N hN n)
    (fun i n hn e => A.leftFiniteDimensional_ext_other_eq_zero Q hAS M hM i n (by omega) e)
    (fun i n hn e => A.leftFiniteDimensional_ext_other_eq_zero Q hAS N hN i n (by omega) e)
    (ProjectiveResolution.lift f PM PN) f (ProjectiveResolution.lift_commutes_zero f PM PN)

noncomputable def rightFiniteDimensionalExtBidualNatIso (hAS : A.ASRegular Q) :
    (A.rightFiniteDimensionalExtThreeFunctor Q hAS).rightOp ⋙
      A.leftFiniteDimensionalExtThreeFunctor Q hAS ≅ 𝟭 A.RightFiniteDimensional :=
  NatIso.ofComponents (fun M => A.rightFiniteDimensionalProperty.isoMk
    (X := ((A.rightFiniteDimensionalExtThreeFunctor Q hAS).rightOp ⋙
      A.leftFiniteDimensionalExtThreeFunctor Q hAS).obj M) (Y := M)
    (A.rightFiniteDimensionalExtBidualIso Q hAS M.obj M.property)) (by
      intro M N f
      exact A.rightFiniteDimensionalExtBidualIso_natural Q hAS M.obj N.obj M.property N.property f)

noncomputable def leftFiniteDimensionalExtBidualNatIso (hAS : A.ASRegular Q) :
    (A.leftFiniteDimensionalExtThreeFunctor Q hAS).rightOp ⋙
      A.rightFiniteDimensionalExtThreeFunctor Q hAS ≅ 𝟭 A.LeftFiniteDimensional :=
  NatIso.ofComponents (fun M => A.leftFiniteDimensionalProperty.isoMk
    (X := ((A.leftFiniteDimensionalExtThreeFunctor Q hAS).rightOp ⋙
      A.rightFiniteDimensionalExtThreeFunctor Q hAS).obj M) (Y := M)
    (A.leftFiniteDimensionalExtBidualIso Q hAS M.obj M.property)) (by
      intro M N f
      exact A.leftFiniteDimensionalExtBidualIso_natural Q hAS M.obj N.obj M.property N.property f)

noncomputable def finiteDimensionalExtThreeEquivalence (hAS : A.ASRegular Q) :
    A.RightFiniteDimensionalᵒᵖ ≌ A.LeftFiniteDimensional :=
  CategoryTheory.Equivalence.mk (A.rightFiniteDimensionalExtThreeFunctor Q hAS)
    (A.leftFiniteDimensionalExtThreeFunctor Q hAS).rightOp
    (NatIso.op (A.rightFiniteDimensionalExtBidualNatIso Q hAS))
    (A.leftFiniteDimensionalExtBidualNatIso Q hAS)
end ASGinzburg.ZAlgebra
