import work.ASGinzburgDraft.TriangleGinzburgLoopCoordinates
import work.ASGinzburgDraft.TriangleGinzburgGLSubstitutionInverse
import work.ASGinzburgDraft.TriangleArrowInvariantContraction

/-! Genuine GL substitutions fix both actual original/dual loop
contractions, hence the literal loop differential. -/
namespace ASGinzburg
universe u
variable (k : Type u) [Field k]

theorem triangleGinzburgGLSubstitution_outgoingLoop (g : TriangleGL333 k) (s : Fin 3) :
    triangle333.ginzburgArrowSubstitutionComponent k (triangleGinzburgGLArrowReplacement k g)
        s s (triangleGinzburgOutgoingLoopCoordinates k s) =
      triangleGinzburgOutgoingLoopCoordinates k s := by
  classical
  unfold triangleGinzburgOutgoingLoopCoordinates
  rw [map_sum]
  simp_rw [CutQuiver.ginzburgArrowSubstitutionComponent_comp,
    triangleGinzburgGLSubstitution_dualCoordinates,triangleGinzburgGLSubstitution_originalCoordinates]
  exact triangleArrow_bilinear_contraction_invariant k
    (triangle333.GinzburgPathComponent k s s)
    (triangleGinzburgOutgoingLoopBilinear k s) (triangleGLArrowMatrix k g s)

theorem triangleGinzburgGLSubstitution_incomingLoop (g : TriangleGL333 k) (s : Fin 3) :
    triangle333.ginzburgArrowSubstitutionComponent k (triangleGinzburgGLArrowReplacement k g)
        (triangleEdgeTarget s) (triangleEdgeTarget s) (triangleGinzburgIncomingLoopCoordinates k s) =
      triangleGinzburgIncomingLoopCoordinates k s := by
  classical
  unfold triangleGinzburgIncomingLoopCoordinates
  rw [map_sum]
  simp_rw [CutQuiver.ginzburgArrowSubstitutionComponent_comp,
    triangleGinzburgGLSubstitution_originalCoordinates,triangleGinzburgGLSubstitution_dualCoordinates]
  exact triangleArrow_bilinear_contraction_invariant k
    (triangle333.GinzburgPathComponent k (triangleEdgeTarget s) (triangleEdgeTarget s))
    (triangleGinzburgIncomingLoopBilinear k s) (triangleGLArrowMatrix k g s)

theorem triangleGinzburgGLSubstitution_incomingLoopAt (g : TriangleGL333 k) (v : Fin 3) :
    triangle333.ginzburgArrowSubstitutionComponent k (triangleGinzburgGLArrowReplacement k g)
        v v (triangleGinzburgIncomingLoopCoordinatesAt k v) =
      triangleGinzburgIncomingLoopCoordinatesAt k v := by
  have h := triangleGinzburgGLSubstitution_incomingLoop k g (triangleEdgePredecessor v)
  fin_cases v <;> exact h

theorem triangleGinzburgGLSubstitution_loopDifferential (g : TriangleGL333 k)
    (v : triangle333.Vertex) :
    triangle333.ginzburgArrowSubstitutionComponent k (triangleGinzburgGLArrowReplacement k g)
        v v (triangle333.ginzburgLoopDifferential k v) =
      triangle333.ginzburgLoopDifferential k v := by
  simp only [triangleGinzburgLoopDifferential_coordinates,map_sub,
    triangleGinzburgGLSubstitution_outgoingLoop,triangleGinzburgGLSubstitution_incomingLoopAt]

end ASGinzburg
