import ASGinzburg.CutQuiver
import Mathlib.Data.Fin.Rev

/-! Reverse the genuine arrows and vertex order while preserving the
cut, so the original winding/positivity conditions remain valid.
This is the quiver required for the left-hand Ginzburg comparison. -/
namespace ASGinzburg.CutQuiver
variable (Q : CutQuiver)

def opposite : CutQuiver where
  vertices := Q.vertices
  arrows := Q.arrows
  at_least_three := Q.at_least_three
  source a := (Q.target a).rev
  target a := (Q.source a).rev
  cut := Q.cut
  forward := by
    intro a ha
    have h := Q.forward a ha
    simp only [Fin.val_rev]
    have hs := (Q.source a).isLt
    have ht := (Q.target a).isLt
    omega
  backward := by
    intro a ha
    have h := Q.backward a ha
    simp only [Fin.val_rev]
    have hs := (Q.source a).isLt
    have ht := (Q.target a).isLt
    omega

def oppositeVertexEquiv : Q.Vertex ≃ Q.opposite.Vertex := Fin.revPerm

def oppositeLiftVertexEquiv : Q.LiftVertex ≃ Q.opposite.LiftVertex where
  toFun v := (v.1.rev,-v.2)
  invFun v := (v.1.rev,-v.2)
  left_inv v := by simp
  right_inv v := by simp

@[simp] theorem opposite_cutDegree (a : Q.Arrow) : Q.opposite.cutDegree a=Q.cutDegree a := rfl

theorem opposite_winding (a : Q.Arrow) : Q.opposite.winding a=Q.winding a := by
  simp only [winding, opposite_cutDegree]
  change ((Q.source a).rev.val : ℤ) - (Q.target a).rev.val +
    (Q.vertices : ℤ) * Q.cutDegree a = _
  simp only [Fin.val_rev]
  have hs := (Q.source a).isLt
  have ht := (Q.target a).isLt
  omega

theorem oppositeLiftVertexEquiv_height (v : Q.LiftVertex) :
    Q.opposite.height (Q.oppositeLiftVertexEquiv v)=
      (Q.vertices:ℤ)-1-Q.height v := by
  simp only [height,oppositeLiftVertexEquiv,Equiv.coe_fn_mk,opposite,Fin.val_rev]
  have hv := v.1.isLt
  have hcast : ((Q.vertices-(v.1.val+1) : ℕ):ℤ)=(Q.vertices:ℤ)-1-v.1.val := by
    omega
  rw [hcast]
  ring

theorem oppositeLiftVertexEquiv_tau (v : Q.LiftVertex) :
    Q.oppositeLiftVertexEquiv (Q.tau v)=Q.opposite.tau.symm (Q.oppositeLiftVertexEquiv v) := by
  apply Prod.ext
  · rfl
  · change -(v.2+1)=-v.2+(-1)
    ring

end ASGinzburg.CutQuiver
