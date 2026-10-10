import work.ASGinzburgDraft.PeriodCutOrdinaryMinimality
import work.ASGinzburgDraft.ASCutOrdinaryResolutions
import ASGinzburg.ASCutGradedResolutionMinimality

/-! Original AS minimality gives actual radical-span image containment
for every differential of the ordinary four-term projective resolution. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem ASRegular.cutOrdinarySimpleProjectiveResolution_minimal_succ
    (hAS : A.ASRegular Q) (x : Q.LiftVertex) (n : ℕ)
    (y : (hAS.cutOrdinarySimpleProjectiveResolution A Q x).complex.X (n+1)) :
    (hAS.cutOrdinarySimpleProjectiveResolution A Q x).complex.d (n+1) n y ∈
      Submodule.span k
        {a : (hAS.cutOrdinarySimpleProjectiveResolution A Q x).complex.X n |
          ∃ r ∈ (hAS.periodIso A Q).cutGradedJacobson Q,
            ∃ m : (hAS.cutOrdinarySimpleProjectiveResolution A Q x).complex.X n,
              MulOpposite.op r • m = a} :=
  (hAS.periodIso A Q).cutGradedMinimalMorphism_ordinary_actionSpan Q
    ((hAS.cutGradedSimpleProjectiveResolution A Q x).complex.d (n+1) n)
    (hAS.cutGradedSimpleProjectiveResolution_minimal A Q x n) y

theorem ASRegular.cutOrdinarySimpleProjectiveResolution_minimal
    (hAS : A.ASRegular Q) (x : Q.LiftVertex) (i j : ℕ)
    (y : (hAS.cutOrdinarySimpleProjectiveResolution A Q x).complex.X i) :
    (hAS.cutOrdinarySimpleProjectiveResolution A Q x).complex.d i j y ∈
      Submodule.span k
        {a : (hAS.cutOrdinarySimpleProjectiveResolution A Q x).complex.X j |
          ∃ r ∈ (hAS.periodIso A Q).cutGradedJacobson Q,
            ∃ m : (hAS.cutOrdinarySimpleProjectiveResolution A Q x).complex.X j,
              MulOpposite.op r • m = a} := by
  by_cases h : j+1=i
  · subst i
    exact hAS.cutOrdinarySimpleProjectiveResolution_minimal_succ A Q x j y
  · rw [(hAS.cutOrdinarySimpleProjectiveResolution A Q x).complex.shape i j h]
    exact Submodule.zero_mem _

end ASGinzburg.ZAlgebra
