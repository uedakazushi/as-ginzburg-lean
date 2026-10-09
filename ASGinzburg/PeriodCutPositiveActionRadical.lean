import ASGinzburg.PeriodCutRadicalCornerEntries
import ASGinzburg.PeriodCutGradedModuleRadical
import ASGinzburg.PeriodCutCornerTotalActions
import ASGinzburg.RightModuleRadical

/-! The cover's genuine positive-action submodules embed into the actual
graded-R radical product. This is the required direction for minimality. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory Opposite
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

theorem cornerModule_positive_action_mem_radical
    (M : (E.cornerCoverZAlgebra Q).RightModule) {x y : Q.LiftVertex}
    (h : Q.heightEquiv x<Q.heightEquiv y) (a : E.CornerCoverHom Q x y)
    (v : E.CornerModuleSpace Q M y) :
    DirectSum.lof k Q.LiftVertex (E.CornerModuleSpace Q M) x
      (E.cornerModuleMap Q M x y a v)∈(E.cornerGradedRightModule Q M).gradedRadicalActionSpan := by
  rw [← E.cutRightRepresentation_corner_lof]
  exact (E.cornerGradedRightModule Q M).gradedRadicalAction_mem a.val
    (E.cornerCoverHom_mem_gradedJacobson Q (by intro he;subst y;exact lt_irrefl _ h) a)
      (DirectSum.lof k Q.LiftVertex (E.CornerModuleSpace Q M) y v)

theorem cornerPositiveActionSpan_lof_mem_radical
    (M : (E.cornerCoverZAlgebra Q).RightModule) (x : Q.LiftVertex)
    (v : E.CornerModuleSpace Q M x)
    (hv : v∈(E.cornerCoverZAlgebra Q).positiveActionSpan M (Q.heightEquiv x)) :
    DirectSum.lof k Q.LiftVertex (E.CornerModuleSpace Q M) x v∈
      (E.cornerGradedRightModule Q M).gradedRadicalActionSpan := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨l,hl,w,a,rfl⟩ := hv
    obtain ⟨y,rfl⟩ := Q.heightEquiv.surjective l
    obtain ⟨b,rfl⟩ := (E.cornerCoordinateHomEquiv Q x y).surjective a
    exact E.cornerModule_positive_action_mem_radical Q M hl b w
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add v w hv hw ihv ihw =>
    rw [map_add]
    exact Submodule.add_mem _ ihv ihw
  | smul c v hv ih =>
    rw [map_smul]
    exact Submodule.smul_mem _ c ih

end ASGinzburg.ZAlgebra.PeriodIso
