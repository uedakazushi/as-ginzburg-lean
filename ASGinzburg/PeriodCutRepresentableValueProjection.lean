import ASGinzburg.PeriodCutRepresentableActionMap
import ASGinzburg.PeriodCutComponentTargetSum

/-! Acting on the concrete generator and taking its genuine ring value
is precisely the actual left-idempotent projection r ↦ e_z r. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

theorem cornerRepresentableValueMap_actionMap_homogeneous (z : Q.LiftVertex) (m : ℕ)
    (r : E.CutGradedBlock (fun t : Q.Vertex => (t.val:ℤ)) m) :
    E.cornerRepresentableValueMap Q z
      (E.cornerRepresentableActionMap Q z
        (E.cutHomogeneousInclusion (fun t : Q.Vertex => (t.val:ℤ)) m r))=
    E.cutVertexIdempotent (fun t : Q.Vertex => (t.val:ℤ)) z.1*
      E.cutHomogeneousInclusion (fun t : Q.Vertex => (t.val:ℤ)) m r := by
  change E.cornerRepresentableValueMap Q z
    ((E.cutRightRepresentation Q ((E.cornerCoverZAlgebra Q).representable (Q.heightEquiv z))
      (E.cutHomogeneousInclusion (fun t : Q.Vertex => (t.val:ℤ)) m r)).unop
        (DirectSum.lof k Q.LiftVertex _ z ((E.cornerCoverZAlgebra Q).id (Q.heightEquiv z))))=_
  rw [E.cutRightRepresentation_homogeneous,E.cutHomogeneousRightOperator_lof,
    E.cutRightColumnMap_apply,map_sum]
  simp only [E.cornerRepresentableValueMap_corner_action,cutCornerEntry_val]
  dsimp only [cutRightSource]
  rw [← Finset.mul_sum,E.sum_cutHomogeneousComponentLinear_target Q m z.1 r]
  change E.cornerRepresentableValueMap Q z (E.cornerRepresentableGenerator Q z)*
    (E.cutVertexIdempotent (fun t : Q.Vertex => (t.val:ℤ)) z.1*
      E.cutHomogeneousInclusion (fun t : Q.Vertex => (t.val:ℤ)) m r)=_
  rw [E.cornerRepresentableValueMap_generator,← mul_assoc]
  congr 1
  exact E.cutVertexIdempotent_mul_self (fun t : Q.Vertex => (t.val:ℤ)) z.1

theorem cornerRepresentableValueMap_actionMap (z : Q.LiftVertex)
    (r : E.CutGradedRing (fun t : Q.Vertex => (t.val:ℤ))) :
    E.cornerRepresentableValueMap Q z (E.cornerRepresentableActionMap Q z r)=
      E.cutVertexIdempotent (fun t : Q.Vertex => (t.val:ℤ)) z.1*r := by
  refine DirectSum.induction_on r ?_ ?_ ?_
  · rw [map_zero,map_zero,mul_zero]
  · intro m r
    exact E.cornerRepresentableValueMap_actionMap_homogeneous Q z m r
  · intro r s hr hs
    rw [map_add,map_add,mul_add,hr,hs]

end ASGinzburg.ZAlgebra.PeriodIso
