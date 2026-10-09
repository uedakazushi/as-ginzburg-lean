import ASGinzburg.PeriodCutRepresentableValueProjection
import ASGinzburg.PeriodCutRightVertexSpaces

/-! The concrete graded representable really has the underlying right
ideal e_z R, via an actual linear equivalence and the usual multiplication. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

noncomputable def cornerRepresentableRightIdealEquiv (z : Q.LiftVertex) :
    (E.cornerGradedRepresentable Q z).space ≃ₗ[k] E.cutRightVertexSpace Q z.1 where
  toFun v := ⟨E.cornerRepresentableValueMap Q z v,E.cornerRepresentableValueMap_target_absorption Q z v⟩
  invFun r := E.cornerRepresentableActionMap Q z r.val
  left_inv v := LinearMap.congr_fun (E.cornerRepresentableActionMap_valueMap Q z) v
  right_inv r := by
    apply Subtype.ext
    change E.cornerRepresentableValueMap Q z (E.cornerRepresentableActionMap Q z r.val)=r.val
    rw [E.cornerRepresentableValueMap_actionMap]
    exact r.property
  map_add' v w := Subtype.ext ((E.cornerRepresentableValueMap Q z).map_add v w)
  map_smul' c v := Subtype.ext ((E.cornerRepresentableValueMap Q z).map_smul c v)

theorem cornerRepresentableActionMap_mul (z : Q.LiftVertex)
    (r s : E.CutGradedRing (fun t : Q.Vertex => (t.val:ℤ))) :
    E.cornerRepresentableActionMap Q z (r*s)=
      ((E.cornerGradedRepresentable Q z).representation s).unop
        (E.cornerRepresentableActionMap Q z r) :=
  (E.cornerGradedRepresentable Q z).representation_mul_apply r s _

theorem cornerRepresentableValueMap_right_action (z : Q.LiftVertex)
    (r : E.CutGradedRing (fun t : Q.Vertex => (t.val:ℤ)))
    (v : (E.cornerGradedRepresentable Q z).space) :
    E.cornerRepresentableValueMap Q z
      (((E.cornerGradedRepresentable Q z).representation r).unop v)=
        E.cornerRepresentableValueMap Q z v*r := by
  have h := E.cornerRepresentableActionMap_mul Q z (E.cornerRepresentableValueMap Q z v) r
  have hi := LinearMap.congr_fun (E.cornerRepresentableActionMap_valueMap Q z) v
  change E.cornerRepresentableActionMap Q z (E.cornerRepresentableValueMap Q z v)=v at hi
  rw [hi] at h
  rw [← h,E.cornerRepresentableValueMap_actionMap,← mul_assoc,
    E.cornerRepresentableValueMap_target_absorption]

end ASGinzburg.ZAlgebra.PeriodIso
