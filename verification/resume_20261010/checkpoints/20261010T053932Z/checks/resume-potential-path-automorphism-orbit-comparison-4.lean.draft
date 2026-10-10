import work.ASGinzburgDraft.PotentialPathAutomorphismAction
import work.ASGinzburgDraft.PotentialPathAutomorphismClasses

/-! The potential equivalence pulled back from the actual cyclic quotient
is exactly the orbit relation of the genuine potential action. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]
attribute [local instance 2000] vertexCutPotentialMulAction

theorem potentialPathAutomorphism_related_iff_smul (φ ψ : Q.Potential k) :
    (Q.potentialPathAutomorphismSetoid k).r φ ψ ↔
      ∃ E : Q.VertexCutPathAutomorphism k, @SMul.smul (Q.VertexCutPathAutomorphism k) (Q.Potential k)
        (Q.vertexCutPotentialMulAction k).toSMul E φ = ψ := by
  rw [Q.potentialPathAutomorphism_related_iff k φ ψ]
  constructor
  · rintro ⟨E,hE⟩
    refine ⟨E, Q.potentialCyclicClass_injective k ?_⟩
    rw [Q.potentialCyclicClass_vertexCut_smul k E φ]
    exact hE
  · rintro ⟨E,rfl⟩
    exact ⟨E,(Q.potentialCyclicClass_vertexCut_smul k E φ).symm⟩

theorem potentialPathAutomorphismSetoid_eq_orbitRel :
    Q.potentialPathAutomorphismSetoid k =
      MulAction.orbitRel (Q.VertexCutPathAutomorphism k) (Q.Potential k) := by
  apply Setoid.ext
  intro φ ψ
  rw [Q.potentialPathAutomorphism_related_iff_smul k φ ψ]
  change (∃ E : Q.VertexCutPathAutomorphism k, @SMul.smul (Q.VertexCutPathAutomorphism k) (Q.Potential k)
        (Q.vertexCutPotentialMulAction k).toSMul E φ = ψ) ↔
    φ ∈ MulAction.orbit (Q.VertexCutPathAutomorphism k) ψ
  rw [MulAction.mem_orbit_symm,MulAction.mem_orbit_iff]

theorem potentialPathAutomorphismClass_eq_iff_smul (φ ψ : Q.Potential k) :
    Q.potentialPathAutomorphismClass k φ = Q.potentialPathAutomorphismClass k ψ ↔
      ∃ E : Q.VertexCutPathAutomorphism k, @SMul.smul (Q.VertexCutPathAutomorphism k) (Q.Potential k)
        (Q.vertexCutPotentialMulAction k).toSMul E φ = ψ := by
  change Quotient.mk (Q.potentialPathAutomorphismSetoid k) φ =
    Quotient.mk (Q.potentialPathAutomorphismSetoid k) ψ ↔ _
  exact Quotient.eq.trans (Q.potentialPathAutomorphism_related_iff_smul k φ ψ)

end ASGinzburg.CutQuiver

namespace ASGinzburg
universe u
variable (k : Type u) [Field k] (Q : CutQuiver)

theorem GinzburgRegularPotential.pathAutomorphismClass_eq_iff_smul
    (φ ψ : GinzburgRegularPotential k Q) :
    φ.pathAutomorphismClass k Q = ψ.pathAutomorphismClass k Q ↔
      ∃ E : Q.VertexCutPathAutomorphism k, @SMul.smul (Q.VertexCutPathAutomorphism k) (Q.Potential k)
        (Q.vertexCutPotentialMulAction k).toSMul E φ.val = ψ.val := by
  change Quotient.mk (ginzburgRegularPotentialPathAutomorphismSetoid k Q) φ =
    Quotient.mk (ginzburgRegularPotentialPathAutomorphismSetoid k Q) ψ ↔ _
  exact Quotient.eq.trans (Q.potentialPathAutomorphism_related_iff_smul k φ.val ψ.val)

end ASGinzburg
