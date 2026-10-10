import work.ASGinzburgDraft.PathCyclicContextTransposition

/-! The linear term of a transposed cut context occurs precisely when
both context paths have length zero. Its actual arrow is the original α. -/
namespace ASGinzburg.CutQuiver
variable (Q : CutQuiver)

theorem Path.endpoints_eq_of_length_zero {i j : Q.Vertex} (p : Q.Path i j)
    (hp : p.length = 0) : i = j := by
  cases p with
  | nil => rfl
  | snoc p a h => simp [Path.length] at hp

theorem pathJacobianContextTranspose_length_one_iff (α β : Q.Arrow)
    (l : Q.Path (Q.target α) (Q.target β))
    (r : Q.Path (Q.source β) (Q.source α)) :
    (Q.pathJacobianContextTranspose α β l r).length = 1 ↔
      l.length = 0 ∧ r.length = 0 := by
  rw [Q.pathJacobianContextTranspose_length]
  omega

theorem pathJacobianContextTranspose_leading_endpoints (α β : Q.Arrow)
    (l : Q.Path (Q.target α) (Q.target β))
    (r : Q.Path (Q.source β) (Q.source α))
    (h : (Q.pathJacobianContextTranspose α β l r).length = 1) :
    Q.source α = Q.source β ∧ Q.target α = Q.target β := by
  obtain ⟨hl, hr⟩ := (Q.pathJacobianContextTranspose_length_one_iff α β l r).mp h
  exact ⟨(r.endpoints_eq_of_length_zero Q hr).symm,
    l.endpoints_eq_of_length_zero Q hl⟩

theorem pathJacobianContextTranspose_leading_word (α β : Q.Arrow)
    (l : Q.Path (Q.target α) (Q.target β))
    (r : Q.Path (Q.source β) (Q.source α))
    (h : (Q.pathJacobianContextTranspose α β l r).length = 1) :
    (Q.pathJacobianContextTranspose α β l r).toList = [α] := by
  obtain ⟨hl, hr⟩ := (Q.pathJacobianContextTranspose_length_one_iff α β l r).mp h
  have hlw : l.toList = [] := List.length_eq_zero_iff.mp (l.length_toList.trans hl)
  have hrw : r.toList = [] := List.length_eq_zero_iff.mp (r.length_toList.trans hr)
  simp only [pathJacobianContextTranspose, Path.toList_comp, Path.toList, hlw, hrw,
    List.nil_append, List.append_nil]

end ASGinzburg.CutQuiver
