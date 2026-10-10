import work.ASGinzburgDraft.ZeroCutIsomorphismTransposedLeading
import work.ASGinzburgDraft.ZeroCutIsomorphismTransposedCoefficientIdentity
import work.ASGinzburgDraft.ZeroCutIsomorphismTransposeArrowChange
import work.ASGinzburgDraft.PathSubstitutionLeadingArrowIdentification
import work.ASGinzburgDraft.ZeroCutIsomorphismTransposedCyclicSubstitution

/-! Original Ginzburg regularity makes the true transposed context
replacement genuinely invertible. Thus a genuine native Jacobian
Z-algebra isomorphism gives the actual potential orbit equality, without
periodic compatibility or any leading-bijectivity hypothesis. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]
variable {φ ψ : Q.Potential k}
variable (F : ZAlgebra.Isomorphism (Q.unrolledJacobianZAlgebra k φ)
  (Q.unrolledJacobianZAlgebra k ψ))
variable (hφ : Q.GinzburgRegular k φ) (hψ : Q.GinzburgRegular k ψ)

theorem zeroCutIsomorphismTransposedLeadingCoordinates_eq_transpose
    (b : Q.Arrow) (hb : Q.cut b = true) :
    Q.zeroCutIsomorphismTransposedLeadingCoordinates k F b hb =
      Q.zeroCutIsomorphismDerivativeTransposeEquiv k F hφ hψ (Q.target b) (Q.source b)
        (Finsupp.single (⟨b, rfl, rfl, hb⟩ :
          Q.FoundationRelationArrow (Q.target b) (Q.source b)) 1) := by
  apply Finsupp.ext
  intro a
  rw [Q.zeroCutIsomorphismTransposedReplacement_leading_coordinates_apply]
  exact Q.zeroCutIsomorphismTransposedConstantCoefficient k F hφ hψ b hb a

theorem zeroCutIsomorphismTransposedReplacement_leading_arrow (a : Q.Arrow) :
    Q.pathArrowProjection k (Q.source a) (Q.target a)
      (Q.zeroCutIsomorphismTransposedReplacement k F a) =
    (Q.zeroCutIsomorphismTransposeArrowLinearEquiv k F hφ hψ
      (Q.source a) (Q.target a) (Q.pathArrowBasisElement k a)).val := by
  rw [← Q.zeroCutIsomorphismTransposeArrowAutomorphism_arrow k F hφ hψ a]
  cases ha : Q.cut a
  · rw [Q.zeroCutIsomorphismTransposedReplacement_noncut_leading_projection k F a ha,
      Q.zeroCutIsomorphismTransposeArrowAutomorphism_noncut_arrow k F hφ hψ a ha]
  · rw [Q.zeroCutIsomorphismTransposedReplacement_leading_projection k F a ha,
      Q.zeroCutIsomorphismTransposedLeadingCoordinates_eq_transpose k F hφ hψ a ha,
      Q.zeroCutIsomorphismTransposeArrowAutomorphism_cut_arrow k F hφ hψ a ha]

include hφ hψ in
theorem zeroCutIsomorphismTransposedReplacement_leading_bijective (i j : Q.Vertex) :
    Function.Bijective
      (Q.pathSubstitutionArrowLinearMap k (Q.zeroCutIsomorphismTransposedReplacement k F) i j) :=
  Q.pathSubstitutionArrowLinearMap_bijective_of_arrow_images k _
    (Q.zeroCutIsomorphismTransposeArrowLinearEquiv k F hφ hψ)
    (Q.zeroCutIsomorphismTransposedReplacement_leading_arrow k F hφ hψ) i j

noncomputable def zeroCutIsomorphismTransposedAutomorphism : Q.VertexCutPathAutomorphism k :=
  Q.invertibleLeadingPathSubstitutionAutomorphism k (Q.zeroCutIsomorphismTransposedReplacement k F)
    (Q.zeroCutIsomorphismTransposedReplacement_mem_cut k F)
    (Q.zeroCutIsomorphismTransposedReplacement_leading_bijective k F hφ hψ)

theorem zeroCutIsomorphismTransposedAutomorphism_arrow (a : Q.Arrow) :
    VertexCutPathAutomorphism.arrowReplacement Q k
      (Q.zeroCutIsomorphismTransposedAutomorphism k F hφ hψ) a =
      Q.zeroCutIsomorphismTransposedReplacement k F a :=
  Q.invertibleLeadingPathSubstitutionAutomorphism_arrow k _ _ _ a

theorem zeroCutIsomorphismTransposedAutomorphism_potential :
    (Q.zeroCutIsomorphismTransposedAutomorphism k F hφ hψ) • ψ =
      (Q.zeroCutIsomorphismPathAutomorphism k F) • φ := by
  apply Subtype.ext
  change (VertexCutPathAutomorphism.potentialLinearEquiv Q k
    (Q.zeroCutIsomorphismTransposedAutomorphism k F hφ hψ) ψ).val = _
  rw [VertexCutPathAutomorphism.potential_val_cyclicSubstitution]
  have hw : VertexCutPathAutomorphism.wordArrowReplacement Q k
      (Q.zeroCutIsomorphismTransposedAutomorphism k F hφ hψ) =
      fun a => Q.pathWordMap k (Q.source a) (Q.target a)
        (Q.zeroCutIsomorphismTransposedReplacement k F a) := by
    funext a
    unfold VertexCutPathAutomorphism.wordArrowReplacement
    rw [Q.zeroCutIsomorphismTransposedAutomorphism_arrow]
  rw [hw]
  exact Q.zeroCutIsomorphismTransposedCyclicSubstitution k F

noncomputable def nativeJacobianIsomorphismPotentialAutomorphism : Q.VertexCutPathAutomorphism k :=
  (Q.zeroCutIsomorphismTransposedAutomorphism k F hφ hψ)⁻¹ *
    Q.zeroCutIsomorphismPathAutomorphism k F

theorem nativeJacobianIsomorphismPotentialAutomorphism_potential :
    (Q.nativeJacobianIsomorphismPotentialAutomorphism k F hφ hψ) • φ = ψ := by
  rw [nativeJacobianIsomorphismPotentialAutomorphism, mul_smul,
    ← Q.zeroCutIsomorphismTransposedAutomorphism_potential k F hφ hψ, inv_smul_smul]

theorem GinzburgRegular.nativeJacobianIsomorphism_potentialOrbit
    (hφ : Q.GinzburgRegular k φ) (hψ : Q.GinzburgRegular k ψ)
    (F : ZAlgebra.Isomorphism (Q.unrolledJacobianZAlgebra k φ)
      (Q.unrolledJacobianZAlgebra k ψ)) :
    ∃ E : Q.VertexCutPathAutomorphism k, E • φ = ψ :=
  ⟨Q.nativeJacobianIsomorphismPotentialAutomorphism k F hφ hψ,
    Q.nativeJacobianIsomorphismPotentialAutomorphism_potential k F hφ hψ⟩

end ASGinzburg.CutQuiver
