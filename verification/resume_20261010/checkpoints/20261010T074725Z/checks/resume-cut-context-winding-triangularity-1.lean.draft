import work.ASGinzburgDraft.PathCyclicContextTransposition

/-! A positive-length context in (3.9) replaces the cut arrow β by
a path containing a cut arrow α with strictly smaller winding degree. -/
namespace ASGinzburg.CutQuiver
variable (Q : CutQuiver)

theorem pathJacobianContextTranspose_winding_sum (α β : Q.Arrow)
    (l : Q.Path (Q.target α) (Q.target β))
    (r : Q.Path (Q.source β) (Q.source α)) :
    (Q.pathJacobianContextTranspose α β l r).winding =
      r.winding + Q.winding α + l.winding := by
  simp [pathJacobianContextTranspose, Path.winding_comp, Path.winding]

theorem pathJacobianContextTranspose_winding_eq (α β : Q.Arrow)
    (l : Q.Path (Q.target α) (Q.target β))
    (r : Q.Path (Q.source β) (Q.source α))
    (hα : Q.cut α = true) (hβ : Q.cut β = true)
    (hl : l.cutDegree = 0) (hr : r.cutDegree = 0) :
    (Q.pathJacobianContextTranspose α β l r).winding = Q.winding β := by
  have h := (Q.pathJacobianContextTranspose α β l r).winding_eq
  rw [Q.pathJacobianContextTranspose_cutDegree α β l r hα hl hr] at h
  simpa only [winding, Q.cutDegree_true hβ, Nat.cast_one, mul_one] using h

theorem cutContext_winding_lt_of_positive_length (α β : Q.Arrow)
    (l : Q.Path (Q.target α) (Q.target β))
    (r : Q.Path (Q.source β) (Q.source α))
    (hα : Q.cut α = true) (hβ : Q.cut β = true)
    (hl : l.cutDegree = 0) (hr : r.cutDegree = 0)
    (hpos : 0 < l.length ∨ 0 < r.length) : Q.winding α < Q.winding β := by
  have heq := Q.pathJacobianContextTranspose_winding_eq α β l r hα hβ hl hr
  rw [Q.pathJacobianContextTranspose_winding_sum] at heq
  have hl₀ := l.winding_nonneg
  have hr₀ := r.winding_nonneg
  rcases hpos with hlpos | hrpos
  · have := l.winding_pos_of_length_pos hlpos
    omega
  · have := r.winding_pos_of_length_pos hrpos
    omega

end ASGinzburg.CutQuiver
