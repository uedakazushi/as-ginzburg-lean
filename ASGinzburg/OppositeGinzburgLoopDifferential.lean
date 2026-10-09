import ASGinzburg.OppositeGinzburgGenerators

/-! The actual sum of arrow/dual-arrow commutators changes sign on reversal. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem oppositeGinzburgPathComponentEquiv_loopDifferential (v : Q.Vertex) :
    Q.oppositeGinzburgPathComponentEquiv k v v (Q.ginzburgLoopDifferential k v) =
      -Q.opposite.ginzburgLoopDifferential k v.rev := by
  classical
  rw [ginzburgLoopDifferential, map_sum, ginzburgLoopDifferential,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  have hs : (Q.opposite.source a = v.rev) ↔ Q.target a = v := by
    change (Q.target a).rev = v.rev ↔ _
    exact Fin.rev_inj
  have ht : (Q.opposite.target a = v.rev) ↔ Q.source a = v := by
    change (Q.source a).rev = v.rev ↔ _
    exact Fin.rev_inj
  by_cases hsa : Q.source a = v <;> by_cases hta : Q.target a = v <;>
    simp [map_sub, hsa, hta, hs, ht, oppositeGinzburgPathComponentEquiv_single,
      GinzburgPath.opposite_transport, GinzburgPath.opposite_comp]

end ASGinzburg.CutQuiver
