import ASGinzburg.OppositeGinzburgGradings
import ASGinzburg.OppositeGinzburgPathDifferential
import ASGinzburg.GinzburgCochainComplex

/-! The genuine differential comparison on every homogeneous finite sum. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem oppositeGinzburgPathComponentEquiv_homogeneousDifferential (φ : Q.Potential k)
    {u v : Q.Vertex} {q : ℤ} {f : Q.GinzburgPathComponent k u v}
    (hf : f ∈ Q.ginzburgCohomologicalComponent k u v q) :
    Q.oppositeGinzburgPathComponentEquiv k u v (Q.ginzburgDifferential k φ u v f) =
      ginzburgSign k (q + 1) •
        Q.opposite.ginzburgDifferential k (Q.oppositePotentialEquiv k φ) v.rev u.rev
          (Q.oppositeGinzburgPathComponentEquiv k u v f) := by
  change f ∈ Finsupp.supported k k _ at hf
  rw [Finsupp.supported_eq_span_single] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p,hp,rfl⟩ := hx
    change p.cohomologicalDegree = q at hp
    rw [← hp]
    exact Q.oppositeGinzburgPathComponentEquiv_pathDifferential k φ p
  | zero => simp
  | add f g hf hg ihf ihg => simp [map_add, ihf, ihg, smul_add]
  | smul a f hf ih =>
    simp only [map_smul, ih]
    exact smul_comm a (ginzburgSign k (q + 1)) _

@[simp] theorem oppositeGinzburgCohomologicalEquiv_coe
    (u v : Q.Vertex) (q : ℤ) (f : Q.ginzburgCohomologicalComponent k u v q) :
    (Q.oppositeGinzburgCohomologicalEquiv k u v q f).val =
      Q.oppositeGinzburgPathComponentEquiv k u v f.val := rfl

theorem oppositeGinzburgCohomologicalEquiv_differential (φ : Q.Potential k)
    (u v : Q.Vertex) (q : ℤ) (f : Q.ginzburgCohomologicalComponent k u v q) :
    Q.oppositeGinzburgCohomologicalEquiv k u v (q + 1)
        (Q.ginzburgGradedDifferential k φ u v q f) =
      ginzburgSign k (q + 1) •
        Q.opposite.ginzburgGradedDifferential k (Q.oppositePotentialEquiv k φ) v.rev u.rev q
          (Q.oppositeGinzburgCohomologicalEquiv k u v q f) := by
  apply Subtype.ext
  exact Q.oppositeGinzburgPathComponentEquiv_homogeneousDifferential k φ f.property

end ASGinzburg.CutQuiver
