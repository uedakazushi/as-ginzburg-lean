import ASGinzburg.ASCutOrdinaryResolutions
import ASGinzburg.ASCutGradedResolutions
import work.ASGinzburgDraft.PeriodCutOrdinaryRightModuleData

/-! The actual ordinary simple projective resolution retains the actual
native graded term data of the same AS resolution. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def ASRegular.cutOrdinarySimpleResolutionTermData
    (hAS : A.ASRegular Q) (i : Q.Vertex) (n : ℕ) :
    GradedOrdinaryModuleData k (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ
      ((hAS.periodIso A Q).cutIntegerOppositeHomogeneousSpace Q) :=
  (hAS.periodIso A Q).cutRightModuleOrdinaryData Q
    ((hAS.cutGradedSimpleProjectiveResolution A Q (i,0)).complex.X n)

theorem ASRegular.cutOrdinarySimpleResolutionTermData_ringModule
    (hAS : A.ASRegular Q) (i : Q.Vertex) (n : ℕ) :
    (hAS.cutOrdinarySimpleResolutionTermData A Q i n).ringModule =
      (hAS.cutOrdinarySimpleProjectiveResolution A Q (i,0)).complex.X n := rfl

theorem ASRegular.cutOrdinarySimpleResolutionTermData_finite
    (hAS : A.ASRegular Q) (i : Q.Vertex) (n : ℕ) :
    Module.Finite (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ
      (hAS.cutOrdinarySimpleResolutionTermData A Q i n).ringModule :=
  Eq.mpr (congrArg
    (fun N : ModuleCat.{v} (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ =>
      Module.Finite (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ N)
    (hAS.cutOrdinarySimpleResolutionTermData_ringModule A Q i n))
    (hAS.cutOrdinarySimpleProjectiveResolution_finite A Q (i,0) n)

theorem ASRegular.cutOrdinarySimpleResolution_d_preservesGrade
    (hAS : A.ASRegular Q) (i : Q.Vertex) (n : ℕ) :
    (hAS.cutOrdinarySimpleResolutionTermData A Q i (n + 1)).PreservesGrade
      (hAS.cutOrdinarySimpleResolutionTermData A Q i n)
      ((hAS.cutOrdinarySimpleProjectiveResolution A Q (i,0)).complex.d (n + 1) n) :=
  (hAS.periodIso A Q).cutRightModuleOrdinaryMap_preservesGrade Q
    ((hAS.cutGradedSimpleProjectiveResolution A Q (i,0)).complex.d (n + 1) n)

end ASGinzburg.ZAlgebra
