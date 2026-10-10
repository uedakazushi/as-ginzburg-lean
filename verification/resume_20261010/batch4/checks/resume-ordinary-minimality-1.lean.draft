import ASGinzburg.PeriodCutGradedMinimality
import ASGinzburg.PeriodCutForgetGrading
import work.ASGinzburgDraft.AlgebraModuleActionSpanRestriction

/-! The genuine graded-radical minimality condition remains an actual
radical action-span condition after forgetting the internal grading. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices : ℤ))

theorem cutGradedMinimalMorphism_ordinary_actionSpan
    {M N : E.CutGradedRightModule Q} (f : M ⟶ N)
    (hf : CutGradedRightModule.IsMinimalMorphism f)
    (x : (E.cutGradedForgetFunctor Q).obj M) :
    (E.cutGradedForgetFunctor Q).map f x ∈ Submodule.span k
      {a : (E.cutGradedForgetFunctor Q).obj N |
        ∃ r ∈ E.cutGradedJacobson Q,
          ∃ m : (E.cutGradedForgetFunctor Q).obj N, MulOpposite.op r • m = a} := by
  have h := algebraModuleRestrictScalarsIso_inv_mem_actionSpan k
    (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))ᵐᵒᵖ N.space
    (MulOpposite.op '' (E.cutGradedJacobson Q : Set _))
    (x := f.val x) (by
      apply Submodule.span_mono _ (hf x)
      rintro a ⟨r, hr, m, hm⟩
      exact ⟨MulOpposite.op r, ⟨r, hr, rfl⟩, m, hm⟩)
  apply Submodule.span_mono _ h
  rintro a ⟨r, ⟨s, hs, rfl⟩, m, hm⟩
  exact ⟨s, hs, m, hm⟩

end ASGinzburg.ZAlgebra.PeriodIso
