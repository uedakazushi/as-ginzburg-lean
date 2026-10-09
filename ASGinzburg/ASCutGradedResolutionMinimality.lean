import ASGinzburg.PeriodCutGradedMinimality
import ASGinzburg.ASResolutionComplexMinimality
import ASGinzburg.ASCutGradedResolutions

/-! Original AS conditions give genuine graded-Jacobson minimality of
every differential in the actual graded-R projective resolution. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem ASRegular.cutGradedSimpleProjectiveResolution_minimal
    (hAS : A.ASRegular Q) (x : Q.LiftVertex) (n : ℕ) :
    PeriodIso.CutGradedRightModule.IsMinimalMorphism
      ((hAS.cutGradedSimpleProjectiveResolution A Q x).complex.d (n+1) n) := by
  change PeriodIso.CutGradedRightModule.IsMinimalMorphism
    ((hAS.periodIso A Q).cornerGradedModuleMap Q
      (((hAS.cutCornerASRegular Q).resolution (hAS.cutCornerCover A Q) Q x).complex.d (n+1) n))
  exact (hAS.periodIso A Q).cornerGradedModuleMap_minimal Q _
    (((hAS.cutCornerASRegular Q).resolution (hAS.cutCornerCover A Q) Q x).complex_d_succ_minimal n)

end ASGinzburg.ZAlgebra
