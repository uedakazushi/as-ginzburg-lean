import ASGinzburg.PathCyclicDerivatives
import ASGinzburg.PathUnrolling

/-! Removing the actual last arrow of a composable path word gives
a composable path with the required endpoint. -/
namespace ASGinzburg.CutQuiver.Path
variable {Q : CutQuiver}

theorem exists_prefix_of_toList_append {u v : Q.Vertex} (p : Q.Path u v)
    (w : List Q.Arrow) (b : Q.Arrow) (h : p.toList=w++[b]) :
    ∃ q : Q.Path u (Q.source b), q.toList=w ∧ Q.target b=v := by
  cases p with
  | nil => simp [toList] at h
  | @snoc x p a ha =>
    have hlast := congrArg List.getLast? h
    have hab : a=b := by simpa [toList] using hlast
    subst a
    refine ⟨p.transport rfl ha.symm, ?_, rfl⟩
    rw [toList_transport]
    exact List.append_cancel_right h

end ASGinzburg.CutQuiver.Path
