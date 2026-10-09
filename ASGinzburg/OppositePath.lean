import ASGinzburg.OppositeCutQuiver
import ASGinzburg.PathLengthFiltration
import ASGinzburg.PathUnrolling

/-! Reversal of genuine composable paths in the reflected opposite quiver.
Both endpoints, the cut degree and the actual arrow word are retained. -/
namespace ASGinzburg.CutQuiver
variable {Q : CutQuiver}

def Path.opposite : {u v : Q.Vertex} → Q.Path u v →
    Q.opposite.Path v.rev u.rev
  | _, _, .nil v => Path.nil (Q := Q.opposite) v.rev
  | _, _, .snoc p a h =>
    ((Path.snoc (Q := Q.opposite) (Path.nil (Q := Q.opposite) (Q.target a).rev) a rfl).transport (Q := Q.opposite)
      rfl (congrArg Fin.rev h)).comp p.opposite

@[simp] theorem Path.opposite_nil (v : Q.Vertex) :
    (Path.nil (Q := Q) v).opposite = Path.nil (Q := Q.opposite) v.rev := by rw [Path.opposite]

theorem Path.opposite_length {u v : Q.Vertex} (p : Q.Path u v) :
    p.opposite.length = p.length := by
  induction p with
  | nil => simp [length]
  | snoc p a h ih =>
    simp [opposite, length_comp, length, ih, Nat.add_comm]

theorem Path.opposite_cutDegree {u v : Q.Vertex} (p : Q.Path u v) :
    p.opposite.cutDegree = p.cutDegree := by
  induction p with
  | nil => simp [cutDegree]
  | snoc p a h ih =>
    simp [opposite, cutDegree_comp, cutDegree, ih, Nat.add_comm]

theorem Path.opposite_toList {u v : Q.Vertex} (p : Q.Path u v) :
    p.opposite.toList = p.toList.reverse := by
  induction p with
  | nil => simp [toList]
  | snoc p a h ih =>
    simp [opposite, toList_comp, toList, ih]

theorem Path.opposite_injective (u v : Q.Vertex) :
    Function.Injective (fun p : Q.Path u v => p.opposite) := by
  intro p q h
  apply Path.toList_injective u v
  have hw := congrArg Path.toList h
  simp only [opposite_toList] at hw
  exact List.reverse_injective hw

end ASGinzburg.CutQuiver
