import work.ASGinzburgDraft.GinzburgVertexWordProjection

/-! Applying the actual first-letter projection recovers a vertex loop
component from an actual finite sum of nonzero-degree loop components. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgVertexWordProjection_sum_pathWordMap_of_cohomological
    (v : Q.Vertex) (q : ℤ) (hq : q ≠ 0)
    (f : ∀ i : Q.Vertex, Q.GinzburgPathComponent k i i)
    (hf : ∀ i, f i ∈ Q.ginzburgCohomologicalComponent k i i q) :
    Q.ginzburgVertexWordProjection k v (∑ i : Q.Vertex, Q.ginzburgPathWordMap k i i (f i)) =
      Q.ginzburgPathWordMap k v v (f v) := by
  classical
  rw [map_sum]
  simp_rw [Q.ginzburgVertexWordProjection_pathWordMap_of_cohomological k v _ _ q hq _ (hf _)]
  simp

end ASGinzburg.CutQuiver
