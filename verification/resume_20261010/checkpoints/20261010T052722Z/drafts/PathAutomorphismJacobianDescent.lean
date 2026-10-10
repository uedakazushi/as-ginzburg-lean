import work.ASGinzburgDraft.PathAutomorphismJacobianChainRule
import work.ASGinzburgDraft.PathAutomorphismJacobianUnrolling
import work.ASGinzburgDraft.ASGinzburgCorrespondenceStatement
import work.ASGinzburgDraft.PotentialPathAutomorphismOrbitComparison

/-! The actual potential-to-AS-algebra map descends to the source's
genuine path-automorphism classes, without a characteristic restriction. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def VertexCutPathAutomorphism.unrolledJacobianIsomorphismOfAction
    (E : Q.VertexCutPathAutomorphism k) (φ : Q.Potential k) :
    ZAlgebra.Isomorphism (Q.unrolledJacobianZAlgebra k φ)
      (Q.unrolledJacobianZAlgebra k
        (VertexCutPathAutomorphism.potentialLinearEquiv Q k E φ)) :=
  VertexCutPathAutomorphism.unrolledJacobianZAlgebraIsomorphism Q k E φ _
    (VertexCutPathAutomorphism.pathJacobianIdeal_mem_iff_image Q k E φ)

theorem unrolledJacobian_isomorphism_of_potentialPathClass
    (φ ψ : Q.Potential k)
    (h : Q.potentialPathAutomorphismClass k φ = Q.potentialPathAutomorphismClass k ψ) :
    Nonempty (ZAlgebra.Isomorphism (Q.unrolledJacobianZAlgebra k φ)
      (Q.unrolledJacobianZAlgebra k ψ)) := by
  obtain ⟨E,hE⟩ := (Q.potentialPathAutomorphismClass_eq_iff_smul k φ ψ).mp h
  change VertexCutPathAutomorphism.potentialLinearEquiv Q k E φ = ψ at hE
  rw [← hE]
  exact ⟨VertexCutPathAutomorphism.unrolledJacobianIsomorphismOfAction Q k E φ⟩

end ASGinzburg.CutQuiver

namespace ASGinzburg
universe u
variable (k : Type u) [Field k] (Q : CutQuiver)

theorem asGinzburgClassDescent : ASGinzburgClassDescentStatement k Q := by
  intro φ ψ h
  apply (GinzburgRegularPotential.asIsomorphismClass_eq_iff k Q φ ψ).mpr
  obtain ⟨E,hE⟩ := (GinzburgRegularPotential.pathAutomorphismClass_eq_iff_smul k Q φ ψ).mp h
  change CutQuiver.VertexCutPathAutomorphism.potentialLinearEquiv Q k E φ.val = ψ.val at hE
  rw [← hE]
  exact ⟨CutQuiver.VertexCutPathAutomorphism.unrolledJacobianIsomorphismOfAction Q k E φ.val⟩

noncomputable def ginzburgRegularPotentialASClassMap :
    GinzburgRegularPotentialPathAutomorphismClass k Q → ASRegularIsomorphismClass.{u,u} k Q :=
  Quotient.lift (GinzburgRegularPotential.asIsomorphismClass k Q)
    (fun φ ψ h => asGinzburgClassDescent k Q φ ψ (Quotient.sound h))

@[simp] theorem ginzburgRegularPotentialASClassMap_apply
    (φ : GinzburgRegularPotential k Q) :
    ginzburgRegularPotentialASClassMap k Q (φ.pathAutomorphismClass k Q) =
      φ.asIsomorphismClass k Q := rfl

end ASGinzburg
