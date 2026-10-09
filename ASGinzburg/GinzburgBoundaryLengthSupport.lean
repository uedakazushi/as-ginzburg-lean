import ASGinzburg.PathJacobianLengthSupport
import ASGinzburg.GinzburgAugmentationIdeal

/-! Genuine degree minus one differential images contain no paths of
length zero or one. This uses the original potential space only. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem Path.originalGinzburg_length {u v : Q.Vertex} (p : Q.Path u v) :
    (p.originalGinzburg Q).length=p.length := by
  rw [←GinzburgPath.length_toList,Path.originalGinzburg_toList,
    List.length_map,Path.length_toList]

theorem originalGinzburgLinearMap_mem_lengthFiltration {u v : Q.Vertex} {n : ℕ}
    {f : Q.PathComponent k u v} (hf : f ∈ Q.pathLengthFiltration k n u v) :
    Q.originalGinzburgLinearMap k u v f ∈
      Finsupp.supported k k {p : Q.GinzburgPath u v | n ≤ p.length} := by
  exact (Finsupp.supported_comap_lmapDomain k k
    (Path.originalGinzburg Q) {p : Q.GinzburgPath u v | n ≤ p.length})
    (Finsupp.supported_mono (fun p hp => by
      change n ≤ (p.originalGinzburg Q).length
      rw [p.originalGinzburg_length Q]
      exact hp) hf)

theorem ginzburgDifferential_negOne_supported_length (φ : Q.Potential k)
    (u v : Q.Vertex) (x : Q.ginzburgCohomologicalComponent k u v (-1)) :
    Q.ginzburgDifferential k φ u v x.val ∈
      Finsupp.supported k k {p : Q.GinzburgPath u v | 2 ≤ p.length} := by
  rw [←Q.originalGinzburgLinearMap_boundaryLift k φ u v x]
  exact Q.originalGinzburgLinearMap_mem_lengthFiltration k
    (Q.ginzburgBoundaryLift_mem_lengthFiltration k φ u v x)

end ASGinzburg.CutQuiver
