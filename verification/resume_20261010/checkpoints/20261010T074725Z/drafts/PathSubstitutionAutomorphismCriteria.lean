import work.ASGinzburgDraft.IdentityLeadingPathSubstitution
import work.ASGinzburgDraft.PathArrowLinearAutomorphism
import ASGinzburg.PathAutomorphismArrowSubstitution
import ASGinzburg.PathAutomorphismComponents

/-! An actual cut-homogeneous arrow replacement with invertible actual
length-one leading maps extends to an actual nonlinear path automorphism.
No inverse replacement or substitution identity is part of the input. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem VertexCutPathAutomorphism.component_of_substitution
    (E : Q.VertexCutPathAutomorphism k) (σ : Q.PathArrowReplacement k)
    (hE : E.val.toAlgHom = Q.pathArrowSubstitution k σ)
    (i j : Q.Vertex) (f : Q.PathComponent k i j) :
    VertexCutPathAutomorphism.componentLinearEquiv Q k E i j f =
      Q.pathArrowSubstitutionComponent k σ i j f := by
  change E.val.toAlgHom ((Q.pathComponentAlgebra k).totalComponent i j f) i j = _
  rw [hE,Q.pathArrowSubstitution_component]
  exact (Q.pathComponentAlgebra k).totalComponent_apply_same i j _

variable (σ : Q.PathArrowReplacement k)
  (hc : ∀ a, σ a ∈ Q.pathCutComponent k (Q.source a) (Q.target a) (Q.cutDegree a : ℤ))
  (hL : ∀ i j, Function.Bijective (Q.pathSubstitutionArrowLinearMap k σ i j))

noncomputable def pathSubstitutionLeadingEquiv (i j : Q.Vertex) :
    Q.pathArrowComponent k i j ≃ₗ[k] Q.pathArrowComponent k i j :=
  LinearEquiv.ofBijective (Q.pathSubstitutionArrowLinearMap k σ i j) (hL i j)

theorem pathSubstitutionLeadingEquiv_arrow (a : Q.Arrow) :
    (Q.pathSubstitutionLeadingEquiv k σ hL (Q.source a) (Q.target a)
      (Q.pathArrowBasisElement k a)).val =
        Q.pathArrowProjection k (Q.source a) (Q.target a) (σ a) := by
  change Q.pathArrowProjection k (Q.source a) (Q.target a)
    (Q.pathArrowSubstitutionComponent k σ (Q.source a) (Q.target a)
      (Q.pathIdentityArrowReplacement k a)) = _
  rw [pathIdentityArrowReplacement,Q.pathArrowSubstitution_arrow]

theorem pathLeadingAutomorphism_arrow (a : Q.Arrow) :
    VertexCutPathAutomorphism.componentLinearEquiv Q k
      (Q.pathArrowLinearAutomorphism k (Q.pathSubstitutionLeadingEquiv k σ hL))
        (Q.source a) (Q.target a) (Q.pathIdentityArrowReplacement k a) =
          Q.pathArrowProjection k (Q.source a) (Q.target a) (σ a) := by
  rw [VertexCutPathAutomorphism.component_of_substitution Q k _ _ (by rfl),
    pathIdentityArrowReplacement,Q.pathArrowSubstitution_arrow]
  exact Q.pathSubstitutionLeadingEquiv_arrow k σ hL a

noncomputable def pathSubstitutionNormalizedReplacement : Q.PathArrowReplacement k :=
  fun a => VertexCutPathAutomorphism.componentLinearEquiv Q k
    ((Q.pathArrowLinearAutomorphism k (Q.pathSubstitutionLeadingEquiv k σ hL))⁻¹)
      (Q.source a) (Q.target a) (σ a)

include hc in
theorem pathSubstitutionNormalizedReplacement_mem_cut (a : Q.Arrow) :
    Q.pathSubstitutionNormalizedReplacement k σ hL a ∈
      Q.pathCutComponent k (Q.source a) (Q.target a) (Q.cutDegree a : ℤ) :=
  (VertexCutPathAutomorphism.component_preserves_cut Q k _ _ _ _ _).mp (hc a)

theorem pathSubstitutionNormalizedReplacement_sub_identity (a : Q.Arrow) :
    Q.pathSubstitutionNormalizedReplacement k σ hL a - Q.pathIdentityArrowReplacement k a ∈
      Q.pathLengthFiltration k 2 (Q.source a) (Q.target a) := by
  let E := Q.pathArrowLinearAutomorphism k (Q.pathSubstitutionLeadingEquiv k σ hL)
  have H : VertexCutPathAutomorphism.componentLinearEquiv Q k (E⁻¹) _ _
      (Q.pathArrowProjection k (Q.source a) (Q.target a) (σ a)) =
        Q.pathIdentityArrowReplacement k a := by
    rw [VertexCutPathAutomorphism.componentLinearEquiv_inv,
      ← Q.pathLeadingAutomorphism_arrow k σ hL a]
    exact LinearEquiv.symm_apply_apply _ _
  change VertexCutPathAutomorphism.componentLinearEquiv Q k (E⁻¹) _ _ (σ a) -
    Q.pathIdentityArrowReplacement k a ∈ _
  rw [← H,← map_sub]
  exact Q.pathAlgEquivComponent_mem_lengthFiltration k (E⁻¹).val
    (VertexCutPathAutomorphism.fixes_vertex Q k (E⁻¹)) 2
    (Q.sub_pathArrowProjection_mem_length_two k _ _
      (Q.pathAutomorphism_arrow_source_ne_target a) (σ a))

noncomputable def invertibleLeadingPathSubstitutionAutomorphism : Q.VertexCutPathAutomorphism k :=
  Q.pathArrowLinearAutomorphism k (Q.pathSubstitutionLeadingEquiv k σ hL) *
    Q.identityLeadingPathSubstitutionAutomorphism k
      (Q.pathSubstitutionNormalizedReplacement k σ hL)
      (Q.pathSubstitutionNormalizedReplacement_mem_cut k σ hc hL)
      (Q.pathSubstitutionNormalizedReplacement_sub_identity k σ hL)

theorem invertibleLeadingPathSubstitutionAutomorphism_arrow (a : Q.Arrow) :
    VertexCutPathAutomorphism.arrowReplacement Q k
      (Q.invertibleLeadingPathSubstitutionAutomorphism k σ hc hL) a = σ a := by
  unfold VertexCutPathAutomorphism.arrowReplacement invertibleLeadingPathSubstitutionAutomorphism
  rw [VertexCutPathAutomorphism.componentLinearEquiv_mul_apply]
  rw [VertexCutPathAutomorphism.component_of_substitution Q k
    (Q.identityLeadingPathSubstitutionAutomorphism k
      (Q.pathSubstitutionNormalizedReplacement k σ hL)
      (Q.pathSubstitutionNormalizedReplacement_mem_cut k σ hc hL)
      (Q.pathSubstitutionNormalizedReplacement_sub_identity k σ hL))
    (Q.pathSubstitutionNormalizedReplacement k σ hL) (by rfl),
    pathIdentityArrowReplacement,Q.pathArrowSubstitution_arrow]
  change VertexCutPathAutomorphism.componentLinearEquiv Q k
      (Q.pathArrowLinearAutomorphism k (Q.pathSubstitutionLeadingEquiv k σ hL)) _ _
    (VertexCutPathAutomorphism.componentLinearEquiv Q k
      ((Q.pathArrowLinearAutomorphism k (Q.pathSubstitutionLeadingEquiv k σ hL))⁻¹) _ _ (σ a)) = _
  rw [VertexCutPathAutomorphism.componentLinearEquiv_inv]
  exact LinearEquiv.apply_symm_apply _ _

theorem invertibleLeadingPathSubstitutionAutomorphism_toAlgHom :
    (Q.invertibleLeadingPathSubstitutionAutomorphism k σ hc hL).val.toAlgHom =
      Q.pathArrowSubstitution k σ := by
  rw [VertexCutPathAutomorphism.substitution]
  congr 1
  funext a
  exact Q.invertibleLeadingPathSubstitutionAutomorphism_arrow k σ hc hL a

end ASGinzburg.CutQuiver
