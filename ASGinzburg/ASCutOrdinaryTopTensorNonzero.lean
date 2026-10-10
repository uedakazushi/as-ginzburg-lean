import ASGinzburg.ASCutOrdinaryResolutionTopTerm
import ASGinzburg.PeriodCutGradedTensorNakayama

/-! Tensoring the actual nonzero top AS resolution term with the native
radical quotient remains nonzero, by its explicit lower grading bound. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem ASRegular.cutOrdinarySimpleTopTensor_not_isZero (hAS : A.ASRegular Q)
    (x : Q.LiftVertex) :
    ¬ IsZero ((balancedTensorLeftFunctor k (hAS.CutGradedAlgebra A Q)
      (hAS.CutGradedAlgebra A Q ⧸ (hAS.periodIso A Q).cutGradedJacobson Q)).obj
        ((hAS.cutOrdinarySimpleProjectiveResolution A Q x).complex.X 3)) := by
  rw [hAS.cutOrdinarySimpleProjectiveResolution_topTerm_eq A Q x]
  intro h
  exact (hAS.periodIso A Q).cornerGradedRepresentable_ringModule_not_isZero Q
    (Q.tau.symm x)
    (((hAS.periodIso A Q).cornerGradedRepresentable Q (Q.tau.symm x)).ringModule_isZero_of_grade_lower_bound_tensor_functor
      (-(Q.tau.symm x).2)
        ((hAS.periodIso A Q).cornerGradedRepresentable_grade_eq_bot_of_lt Q (Q.tau.symm x)) h)

end ASGinzburg.ZAlgebra
