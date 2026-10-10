import work.ASGinzburgDraft.ASCutOrdinarySimpleGradedResolution
import ASGinzburg.PeriodCutGradedForgetExactness
import ASGinzburg.MapProjectiveResolutionOfTerms

/-! The actual native graded AS resolution can be mapped literally
through the grading forgetful functor to an ordinary simple resolution. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

 theorem ASRegular.cutForgottenGradedSimpleResolution_term_projective
    (hAS : A.ASRegular Q) (i : Q.Vertex) (n : ℕ) :
    Projective (((hAS.periodIso A Q).cutGradedForgetFunctor Q).obj
      ((hAS.cutGradedSimpleProjectiveResolution A Q (i,0)).complex.X n)) := by
  change Projective (hAS.cutOrdinarySimpleResolutionTermData A Q i n).ringModule
  rw [hAS.cutOrdinarySimpleResolutionTermData_ringModule A Q i n]
  exact (hAS.cutOrdinarySimpleProjectiveResolution A Q (i,0)).projective n

noncomputable def ASRegular.cutForgottenGradedSimpleProjectiveResolution
    (hAS : A.ASRegular Q) (i : Q.Vertex) :
    ProjectiveResolution (hAS.cutOrdinarySimple A Q (i,0)) :=
  mapProjectiveResolutionOfTerms ((hAS.periodIso A Q).cutGradedForgetFunctor Q)
    (hAS.cutGradedSimpleProjectiveResolution A Q (i,0))
    (hAS.cutForgottenGradedSimpleResolution_term_projective A Q i)

 theorem ASRegular.cutForgottenGradedSimpleResolution_termData_ringModule
    (hAS : A.ASRegular Q) (i : Q.Vertex) (n : ℕ) :
    (hAS.cutOrdinarySimpleResolutionTermData A Q i n).ringModule =
      (hAS.cutForgottenGradedSimpleProjectiveResolution A Q i).complex.X n := rfl

 theorem ASRegular.cutForgottenGradedSimpleResolution_d
    (hAS : A.ASRegular Q) (i : Q.Vertex) (n : ℕ) :
    (hAS.cutForgottenGradedSimpleProjectiveResolution A Q i).complex.d (n+1) n =
      ((hAS.periodIso A Q).cutGradedForgetFunctor Q).map
        ((hAS.cutGradedSimpleProjectiveResolution A Q (i,0)).complex.d (n+1) n) := rfl

 theorem ASRegular.cutForgottenGradedSimpleResolution_d_preservesGrade
    (hAS : A.ASRegular Q) (i : Q.Vertex) (n : ℕ) :
    (hAS.cutOrdinarySimpleResolutionTermData A Q i (n+1)).PreservesGrade
      (hAS.cutOrdinarySimpleResolutionTermData A Q i n)
      ((hAS.cutForgottenGradedSimpleProjectiveResolution A Q i).complex.d (n+1) n) :=
  (hAS.periodIso A Q).cutRightModuleOrdinaryMap_preservesGrade Q
    ((hAS.cutGradedSimpleProjectiveResolution A Q (i,0)).complex.d (n+1) n)

 theorem ASRegular.cutForgottenGradedSimpleResolution_isZero_ge_four
    (hAS : A.ASRegular Q) (i : Q.Vertex) (n : ℕ) :
    IsZero ((hAS.cutForgottenGradedSimpleProjectiveResolution A Q i).complex.X (n+4)) :=
  mapProjectiveResolutionOfTerms_isZero ((hAS.periodIso A Q).cutGradedForgetFunctor Q)
    (hAS.cutGradedSimpleProjectiveResolution A Q (i,0))
    (hAS.cutForgottenGradedSimpleResolution_term_projective A Q i) (n+4)
    (hAS.cutGradedSimpleProjectiveResolution_isZero_ge_four A Q (i,0) n)

end ASGinzburg.ZAlgebra
