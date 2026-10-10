import work.ASGinzburgDraft.PeriodCutRepresentableBoundedness
import work.ASGinzburgDraft.ASCutOrdinaryResolutions

/-! The genuine top term of the ordinary AS simple resolution is the
cover representable at tau inverse, with its nonzero identity generator
and explicit lower bound on the actual integer grading. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem ASRegular.cutGradedSimpleProjectiveResolution_topTerm_eq
    (hAS : A.ASRegular Q) (x : Q.LiftVertex) :
    (hAS.cutGradedSimpleProjectiveResolution A Q x).complex.X 3=
      (hAS.periodIso A Q).cornerGradedRepresentable Q (Q.tau.symm x) := by
  change (hAS.periodIso A Q).cornerGradedRightModule Q
      ((hAS.cutCornerCover A Q).representable (Q.height (Q.tau.symm x)))=
    (hAS.periodIso A Q).cornerGradedRightModule Q
      ((hAS.cutCornerCover A Q).representable (Q.heightEquiv (Q.tau.symm x)))
  rw [Q.heightEquiv_apply]

theorem ASRegular.cutOrdinarySimpleProjectiveResolution_topTerm_eq
    (hAS : A.ASRegular Q) (x : Q.LiftVertex) :
    (hAS.cutOrdinarySimpleProjectiveResolution A Q x).complex.X 3=
      ((hAS.periodIso A Q).cornerGradedRepresentable Q (Q.tau.symm x)).ringModule := by
  change ((hAS.periodIso A Q).cornerGradedRightModule Q
      ((hAS.cutCornerCover A Q).representable (Q.height (Q.tau.symm x)))).ringModule=
    ((hAS.periodIso A Q).cornerGradedRightModule Q
      ((hAS.cutCornerCover A Q).representable (Q.heightEquiv (Q.tau.symm x)))).ringModule
  rw [Q.heightEquiv_apply]

theorem ASRegular.cutGradedSimpleProjectiveResolution_topTerm_grade_lower_bound
    (hAS : A.ASRegular Q) (x : Q.LiftVertex) (q : ℤ)
    (hq : q < -(Q.tau.symm x).2) :
    ((hAS.cutGradedSimpleProjectiveResolution A Q x).complex.X 3).grade q=⊥ := by
  rw [hAS.cutGradedSimpleProjectiveResolution_topTerm_eq A Q x]
  exact (hAS.periodIso A Q).cornerGradedRepresentable_grade_eq_bot_of_lt Q (Q.tau.symm x) q hq

theorem ASRegular.cutOrdinarySimpleProjectiveResolution_topTerm_not_isZero
    (hAS : A.ASRegular Q) (x : Q.LiftVertex) :
    ¬ IsZero ((hAS.cutOrdinarySimpleProjectiveResolution A Q x).complex.X 3) := by
  rw [hAS.cutOrdinarySimpleProjectiveResolution_topTerm_eq A Q x]
  exact (hAS.periodIso A Q).cornerGradedRepresentable_ringModule_not_isZero Q (Q.tau.symm x)

end ASGinzburg.ZAlgebra
