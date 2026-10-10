import ASGinzburg.ASCutGradedResolutions
import ASGinzburg.ASCutGradedRegularExt
import work.ASGinzburgDraft.ProjectiveResolutionTopHomExactness

/-! The actual final graded Hom differential is surjective in every
internal degree other than the AS top degree, from original AS regularity. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

 theorem ASRegular.cutGradedSimpleHom_regular_top_surjective_other
    (hAS : A.ASRegular Q) (i : Q.Vertex) (q : ℤ) (hq : q ≠ -1)
    (f : (hAS.cutGradedSimpleProjectiveResolution A Q (i,0)).complex.X 3 ⟶
      (((hAS.periodIso A Q).cutRegularGradedRightModule Q).shifted q)) :
    ∃ g : (hAS.cutGradedSimpleProjectiveResolution A Q (i,0)).complex.X 2 ⟶
      (((hAS.periodIso A Q).cutRegularGradedRightModule Q).shifted q),
      (hAS.cutGradedSimpleProjectiveResolution A Q (i,0)).complex.d 3 2 ≫ g = f := by
  apply ProjectiveResolution.hom_three_surjective_of_actual_ext_three_zero _
    (hAS.cutGradedSimpleProjectiveResolution_isZero_ge_four A Q (i,0) 0)
  intro e
  apply hAS.cutGradedRegularExt_other_eq_zero A Q i 3 q _ e
  intro h
  exact hq (congrArg Prod.snd h)

end ASGinzburg.ZAlgebra
