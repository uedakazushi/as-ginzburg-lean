import ASGinzburg.OppositePath

/-! The inverse uses the actual arrows of Q, rather than assuming that
opposite path spaces are isomorphic. -/
namespace ASGinzburg.CutQuiver
variable {Q : CutQuiver}

def Path.unopposite : {u v : Q.opposite.Vertex} → Q.opposite.Path u v →
    Q.Path v.rev u.rev
  | _, _, .nil v => Path.nil (Q := Q) v.rev
  | _, _, .snoc p a h =>
    ((Path.snoc (Q := Q) (Path.nil (Q := Q) (Q.source a)) a rfl).transport
      (Fin.rev_rev (Q.source a)).symm
      (by have hh := congrArg Fin.rev h; simpa [CutQuiver.opposite] using hh)).comp
      p.unopposite

@[simp] theorem Path.unopposite_nil (v : Q.opposite.Vertex) :
    (Path.nil (Q := Q.opposite) v).unopposite = Path.nil (Q := Q) v.rev := by
  rw [Path.unopposite]

theorem Path.unopposite_toList {u v : Q.opposite.Vertex}
    (p : Q.opposite.Path u v) : p.unopposite.toList = p.toList.reverse := by
  induction p with
  | nil => simp [toList]
  | snoc p a h ih => simp [unopposite, toList_comp, toList, ih]

def oppositePathEquiv (u v : Q.Vertex) :
    Q.Path u v ≃ Q.opposite.Path v.rev u.rev where
  toFun := Path.opposite
  invFun p := p.unopposite.transport (Fin.rev_rev u) (Fin.rev_rev v)
  left_inv p := by
    apply Path.toList_injective (Q := Q) u v
    simp [Path.unopposite_toList, Path.opposite_toList]
  right_inv p := by
    apply Path.toList_injective (Q := Q.opposite) v.rev u.rev
    simp [Path.unopposite_toList, Path.opposite_toList]

end ASGinzburg.CutQuiver
