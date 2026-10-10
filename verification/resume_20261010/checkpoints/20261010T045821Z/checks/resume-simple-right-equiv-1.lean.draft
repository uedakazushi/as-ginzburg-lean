import work.ASGinzburgDraft.PeriodCutSimpleCharacters
import work.ASGinzburgDraft.PeriodCutVertexRightModule

/-! The genuine cover total simple is right-R-linearly equivalent to
the actual vertex character module. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

noncomputable def cornerSimpleVertexRightLinearEquiv (z : Q.LiftVertex) :
    letI := E.cutVertexRightModule Q z.1
    (E.cornerGradedRightModule Q
      ((E.cornerCoverZAlgebra Q).simpleRightModule (Q.height z))).ringModule ≃ₗ[
        (E.CutGradedRing (fun t : Q.Vertex => (t.val:ℤ)))ᵐᵒᵖ] k := by
  letI := E.cutVertexRightModule Q z.1
  exact {
    (E.cornerSimpleTotalFieldEquiv Q z).toAddEquiv with
    map_smul' := fun r x => E.cornerSimpleTotalFieldEquiv_right_action Q z r.unop x
  }

noncomputable def cornerSimpleSheetRightIso (i : Q.Vertex) (s t : ℤ) :
    (E.cornerGradedRightModule Q
      ((E.cornerCoverZAlgebra Q).simpleRightModule (Q.height (i,s)))).ringModule ≅
    (E.cornerGradedRightModule Q
      ((E.cornerCoverZAlgebra Q).simpleRightModule (Q.height (i,t)))).ringModule := by
  letI := E.cutVertexRightModule Q i
  exact ((E.cornerSimpleVertexRightLinearEquiv Q (i,s)).trans
    (E.cornerSimpleVertexRightLinearEquiv Q (i,t)).symm).toModuleIso

end ASGinzburg.ZAlgebra.PeriodIso
