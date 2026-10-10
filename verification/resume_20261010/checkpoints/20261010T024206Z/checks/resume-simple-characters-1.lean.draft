import ASGinzburg.OneDimensionalRightRepresentationCharacter
import ASGinzburg.PeriodCutGradedSimpleGrading
import ASGinzburg.PeriodCutModuleIdempotentAction
import ASGinzburg.PeriodCutCharacterClassification

/-! The actual total space of each cover vertex simple carries precisely
its genuine augmentation character, for every integer sheet. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

noncomputable def cornerSimpleTotalFieldEquiv (z : Q.LiftVertex) :
    E.CornerModuleTotalSpace Q
      ((E.cornerCoverZAlgebra Q).simpleRightModule (Q.height z)) ≃ₗ[k] k := by
  refine (E.cornerSimpleTotalSpaceEquiv Q z).trans ?_
  change (((E.cornerCoverZAlgebra Q).rightModuleEvaluation (Q.heightEquiv z)).obj
    ((E.cornerCoverZAlgebra Q).simpleRightModule (Q.height z))) ≃ₗ[k] k
  rw [Q.heightEquiv_apply]
  exact ((E.cornerCoverZAlgebra Q).simpleRightModuleDiagonalIso (Q.height z)).toLinearEquiv.trans
    ((E.cornerCoverZAlgebra Q).scalarEndEquiv (Q.height z)).symm

theorem cornerSimpleTotal_vertex_action (z : Q.LiftVertex) (j : Q.Vertex)
    (x : E.CornerModuleTotalSpace Q
      ((E.cornerCoverZAlgebra Q).simpleRightModule (Q.height z))) :
    (E.cutRightRepresentation Q ((E.cornerCoverZAlgebra Q).simpleRightModule (Q.height z))
      (E.cutVertexIdempotent (fun t : Q.Vertex => (t.val:ℤ)) j)).unop x=
        if j=z.1 then x else 0 := by
  classical
  have hx := (E.cornerSimpleTotalSpaceEquiv Q z).symm_apply_apply x
  change DirectSum.lof k Q.LiftVertex _ z (E.cornerSimpleTotalSpaceEquiv Q z x)=x at hx
  conv_lhs => rw [← hx]
  by_cases h : j=z.1
  · subst j
    rw [if_pos rfl]
    exact (E.cutRightRepresentation_vertex_lof_self Q _ z.1 z.2 _).trans hx
  · rw [if_neg h]
    exact E.cutRightRepresentation_vertex_lof_off Q _ j z (Ne.symm h) _

theorem cornerSimpleTotal_positive_action (z : Q.LiftVertex) (m : ℕ)
    (a : E.CutGradedBlock (fun t : Q.Vertex => (t.val:ℤ)) (m+1))
    (x : E.CornerModuleTotalSpace Q
      ((E.cornerCoverZAlgebra Q).simpleRightModule (Q.height z))) :
    (E.cutRightRepresentation Q ((E.cornerCoverZAlgebra Q).simpleRightModule (Q.height z))
      (E.cutHomogeneousInclusion (fun t : Q.Vertex => (t.val:ℤ)) (m+1) a)).unop x=0 := by
  let M := E.cornerGradedRightModule Q
    ((E.cornerCoverZAlgebra Q).simpleRightModule (Q.height z))
  have hx : x∈M.grade (-z.2) := by
    change x∈E.cornerModuleGrade Q _ (-z.2)
    rw [E.cornerSimpleGrade_diagonal Q z]
    exact Submodule.mem_top
  have hy := M.homogeneous (m+1) a (-z.2) x hx
  change (E.cutRightRepresentation Q _
    (E.cutHomogeneousInclusion (fun t : Q.Vertex => (t.val:ℤ)) (m+1) a)).unop x∈
      E.cornerModuleGrade Q _ (-z.2+((m+1:ℕ):ℤ)) at hy
  rw [E.cornerSimpleGrade_off Q z _ (by omega)] at hy
  exact hy

noncomputable def cornerSimpleCharacter (z : Q.LiftVertex) :
    E.CutGradedRing (fun t : Q.Vertex => (t.val:ℤ)) →ₐ[k] k :=
  oneDimensionalRightRepresentationCharacter
    (E.cutRightRepresentation Q ((E.cornerCoverZAlgebra Q).simpleRightModule (Q.height z)))
    (E.cornerSimpleTotalFieldEquiv Q z)

theorem cornerSimpleCharacter_eq_vertex (z : Q.LiftVertex) :
    E.cornerSimpleCharacter Q z=E.cutVertexCharacter Q z.1 := by
  apply E.cutCharacter_eq_vertex Q _ z.1
  · intro j
    rw [cornerSimpleCharacter,oneDimensionalRightRepresentationCharacter_apply,
      E.cornerSimpleTotal_vertex_action Q z j]
    split_ifs
    · exact (E.cornerSimpleTotalFieldEquiv Q z).apply_symm_apply 1
    · exact map_zero _
  · intro m a
    rw [cornerSimpleCharacter,oneDimensionalRightRepresentationCharacter_apply,
      E.cornerSimpleTotal_positive_action Q z m a,map_zero]

theorem cornerSimpleTotalFieldEquiv_right_action (z : Q.LiftVertex)
    (r : E.CutGradedRing (fun t : Q.Vertex => (t.val:ℤ)))
    (x : E.CornerModuleTotalSpace Q
      ((E.cornerCoverZAlgebra Q).simpleRightModule (Q.height z))) :
    E.cornerSimpleTotalFieldEquiv Q z
      ((E.cutRightRepresentation Q ((E.cornerCoverZAlgebra Q).simpleRightModule (Q.height z)) r).unop x)=
        E.cutVertexCharacter Q z.1 r*(E.cornerSimpleTotalFieldEquiv Q z x) := by
  have h := oneDimensionalRightRepresentation_scalar_action
    (E.cutRightRepresentation Q ((E.cornerCoverZAlgebra Q).simpleRightModule (Q.height z)))
    (E.cornerSimpleTotalFieldEquiv Q z) r x
  change _=E.cornerSimpleCharacter Q z r*_ at h
  rw [E.cornerSimpleCharacter_eq_vertex Q z] at h
  exact h

end ASGinzburg.ZAlgebra.PeriodIso
