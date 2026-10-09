import ASGinzburg.PathLengthFiltration
import ASGinzburg.PathCyclicDerivativeDegrees
import ASGinzburg.GinzburgJacobianBoundaries

/-! The original potential condition forces every genuine Jacobian
relation and every degree-zero boundary to have path length at least two. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem pathJacobianIdeal_le_lengthFiltration (φ : Q.Potential k) (u v : Q.Vertex) :
    (Q.pathJacobianIdeal k φ).hom u v ≤ Q.pathLengthFiltration k 2 u v := by
  apply Q.generatedPathIdeal_le k _ (Q.pathLengthIdeal k 2) _ u v
  intro u v f hf
  obtain ⟨a,hu,hv,rfl⟩ := hf
  subst u v
  exact Finsupp.supported_mono (fun p hp => hp.1)
    (Q.pathCyclicDerivative_supported_degrees k a φ)

theorem ginzburgBoundaryLift_mem_lengthFiltration (φ : Q.Potential k) (u v : Q.Vertex)
    (x : Q.ginzburgCohomologicalComponent k u v (-1)) :
    Q.ginzburgBoundaryLift k φ u v x ∈ Q.pathLengthFiltration k 2 u v :=
  Q.pathJacobianIdeal_le_lengthFiltration k φ u v
    (Q.ginzburgBoundaryLift_mem_pathJacobianIdeal k φ u v x)

end ASGinzburg.CutQuiver
