import ASGinzburg.ASCutGradedResolutions
import ASGinzburg.ASCutGradedRegularExt
import work.ASGinzburgDraft.ProjectiveResolutionLowHomExactness

/-! Original AS regularity gives actual low Hom-complex exactness
against every internal shift of the actual cut regular module. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem ASRegular.cutGradedSimpleHomComplex_regular_exact_low
    (hAS : A.ASRegular Q) (i : Q.Vertex) (q : ℤ) (n : ℕ) (hn : n < 3) :
    ((hAS.cutGradedSimpleProjectiveResolution A Q (i,0)).homComplex (k := k)
      (((hAS.periodIso A Q).cutRegularGradedRightModule Q).shifted q)).ExactAt n := by
  apply ProjectiveResolution.homComplex_exactAt_low_of_actual_ext_zero _ _ n hn
  intro e
  apply hAS.cutGradedRegularExt_other_eq_zero A Q i n q _ e
  intro h
  have hs := congrArg Prod.fst h
  change n = 3 at hs
  omega

end ASGinzburg.ZAlgebra
