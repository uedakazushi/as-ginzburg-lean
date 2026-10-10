import ASGinzburg.PathAutomorphismCyclicSubstitution
import ASGinzburg.PathAutomorphismIdealTransport
import ASGinzburg.PathOccurrenceContextWords
import ASGinzburg.NonlinearCyclicDerivativeChainRule

/-! The actual nonlinear path cyclic chain rule and genuine Jacobian
ideal invariance. Compatibility is derived from occurrence expansion. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem VertexCutPathAutomorphism.pathCyclicDerivative_chainRule
    (E : Q.VertexCutPathAutomorphism k) (φ : Q.Potential k) (b : Q.Arrow) :
    Q.pathCyclicDerivative k b (VertexCutPathAutomorphism.potentialLinearEquiv Q k E φ) =
      ∑ a, Q.pathOccurrenceDerivative k b (Q.source a) (Q.target a)
        (VertexCutPathAutomorphism.arrowReplacement Q k E a)
        (VertexCutPathAutomorphism.componentLinearEquiv Q k E (Q.target a) (Q.source a)
          (Q.pathCyclicDerivative k a φ)) := by
  apply Q.pathWordMap_injective k
  rw [Q.pathWordMap_pathCyclicDerivative,
    VertexCutPathAutomorphism.potential_val_cyclicSubstitution,
    nonlinear_cyclicDerivative_chainRule, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Q.pathWordMap_occurrenceDerivative, VertexCutPathAutomorphism.wordMap_component,
    Q.pathWordMap_pathCyclicDerivative]
  rfl

theorem VertexCutPathAutomorphism.pathCyclicDerivative_mem_ideal_of_images
    (E : Q.VertexCutPathAutomorphism k) (φ : Q.Potential k) (I : Q.PathLinearIdeal k)
    (hI : ∀ a, VertexCutPathAutomorphism.componentLinearEquiv Q k E
      (Q.target a) (Q.source a) (Q.pathCyclicDerivative k a φ) ∈ I.hom (Q.target a) (Q.source a))
    (b : Q.Arrow) :
    Q.pathCyclicDerivative k b (VertexCutPathAutomorphism.potentialLinearEquiv Q k E φ) ∈
      I.hom (Q.target b) (Q.source b) := by
  rw [VertexCutPathAutomorphism.pathCyclicDerivative_chainRule]
  apply Submodule.sum_mem
  intro a ha
  exact Q.pathOccurrenceDerivative_mem_ideal k b (Q.source a) (Q.target a) _ I _ (hI a)

theorem VertexCutPathAutomorphism.pathJacobianIdeal_le_transport
    (E : Q.VertexCutPathAutomorphism k) (φ : Q.Potential k) (i j : Q.Vertex) :
    (Q.pathJacobianIdeal k (VertexCutPathAutomorphism.potentialLinearEquiv Q k E φ)).hom i j ≤
      (VertexCutPathAutomorphism.transportIdeal Q k E (Q.pathJacobianIdeal k φ)).hom i j := by
  apply Q.generatedPathIdeal_le k _
    (VertexCutPathAutomorphism.transportIdeal Q k E (Q.pathJacobianIdeal k φ)) _ i j
  intro i j f hf
  obtain ⟨a,hi,hj,rfl⟩ := hf
  subst i j
  apply VertexCutPathAutomorphism.pathCyclicDerivative_mem_ideal_of_images
  intro a
  exact (VertexCutPathAutomorphism.image_mem_transportIdeal Q k E
    (Q.pathJacobianIdeal k φ) _ _ _).mpr (Q.pathCyclicDerivative_mem_pathJacobianIdeal k φ a)

theorem VertexCutPathAutomorphism.pathJacobianIdeal_mem_iff_image
    (E : Q.VertexCutPathAutomorphism k) (φ : Q.Potential k) (i j : Q.Vertex)
    (f : Q.PathComponent k i j) :
    f ∈ (Q.pathJacobianIdeal k φ).hom i j ↔
      VertexCutPathAutomorphism.componentLinearEquiv Q k E i j f ∈
        (Q.pathJacobianIdeal k (VertexCutPathAutomorphism.potentialLinearEquiv Q k E φ)).hom i j := by
  constructor
  · intro hf
    let ψ := VertexCutPathAutomorphism.potentialLinearEquiv Q k E φ
    have hφ : VertexCutPathAutomorphism.potentialLinearEquiv Q k (E⁻¹) ψ = φ :=
      (VertexCutPathAutomorphism.potentialLinearEquiv Q k E).symm_apply_apply φ
    have hmem : f ∈ (Q.pathJacobianIdeal k
        (VertexCutPathAutomorphism.potentialLinearEquiv Q k (E⁻¹) ψ)).hom i j := by
      rw [hφ]
      exact hf
    have H := VertexCutPathAutomorphism.pathJacobianIdeal_le_transport Q k (E⁻¹) ψ i j hmem
    rw [VertexCutPathAutomorphism.mem_transportIdeal] at H
    simpa only [inv_inv] using H
  · intro hf
    have H := VertexCutPathAutomorphism.pathJacobianIdeal_le_transport Q k E φ i j hf
    rw [VertexCutPathAutomorphism.mem_transportIdeal,
      VertexCutPathAutomorphism.componentLinearEquiv_inv, LinearEquiv.symm_apply_apply] at H
    exact H

end ASGinzburg.CutQuiver
