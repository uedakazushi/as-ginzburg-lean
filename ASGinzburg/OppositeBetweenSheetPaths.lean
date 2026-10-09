import ASGinzburg.OppositePathCutEquiv
import ASGinzburg.JacobianCutQuotientProducts

/-! Reflection reverses the actual endpoint sheets as well as the arrows. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def oppositeBetweenSheetPathCutEquiv (u v : Q.LiftVertex) :
    Q.pathCutComponent k u.1 v.1 (v.2 - u.2) ≃ₗ[k]
      Q.opposite.pathCutComponent k (Q.oppositeLiftVertexEquiv v).1
        (Q.oppositeLiftVertexEquiv u).1
        ((Q.oppositeLiftVertexEquiv u).2 - (Q.oppositeLiftVertexEquiv v).2) :=
  (Q.oppositePathCutEquiv k u.1 v.1 (v.2 - u.2)).trans
    (LinearEquiv.ofEq _ _ (by
      change Q.opposite.pathCutComponent k v.1.rev u.1.rev (v.2 - u.2) =
        Q.opposite.pathCutComponent k v.1.rev u.1.rev (-u.2 - -v.2)
      congr 1
      ring))

@[simp] theorem oppositeBetweenSheetPathCutEquiv_coe (u v : Q.LiftVertex)
    (f : Q.pathCutComponent k u.1 v.1 (v.2 - u.2)) :
    (Q.oppositeBetweenSheetPathCutEquiv k u v f).val =
      Q.oppositePathComponentEquiv k u.1 v.1 f.val := rfl

theorem oppositeBetweenSheetPathCutEquiv_comp {u v w : Q.LiftVertex}
    (f : Q.pathCutComponent k u.1 v.1 (v.2 - u.2))
    (g : Q.pathCutComponent k v.1 w.1 (w.2 - v.2)) :
    Q.oppositeBetweenSheetPathCutEquiv k u w (Q.pathCutCompBetweenLinear k g f) =
      Q.opposite.pathCutCompBetweenLinear k
        (Q.oppositeBetweenSheetPathCutEquiv k u v f)
        (Q.oppositeBetweenSheetPathCutEquiv k v w g) := by
  apply Subtype.ext
  exact Q.oppositePathComponentEquiv_comp k f.val g.val

end ASGinzburg.CutQuiver
