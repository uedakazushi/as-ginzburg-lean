import work.ASGinzburgDraft.NoncutJacobianContextLeadingTerms

/-! A finite family of genuine context expansions has an actual leading
coefficient vector. Its α coordinate is the constant β context coefficient. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def noncutJacobianContextLeadingAggregationCoordinates
    (b : Q.Arrow) (hb : Q.cut b = true)
    (f : ∀ a : {a : Q.Arrow // Q.cut a = true},
      Q.NoncutJacobianContextIndex (Q.target a.val) (Q.source a.val) →₀ k) :
    Q.FoundationRelationArrow (Q.target b) (Q.source b) →₀ k :=
  ∑ a : {a : Q.Arrow // Q.cut a = true},
    Q.noncutJacobianContextTransposedLeadingCoordinates k a b hb (f a)

theorem noncutJacobianContextLeadingAggregationCoordinates_apply
    (b : Q.Arrow) (hb : Q.cut b = true)
    (f : ∀ a : {a : Q.Arrow // Q.cut a = true},
      Q.NoncutJacobianContextIndex (Q.target a.val) (Q.source a.val) →₀ k)
    (a : Q.FoundationRelationArrow (Q.target b) (Q.source b)) :
    Q.noncutJacobianContextLeadingAggregationCoordinates k b hb f a =
      (Q.noncutJacobianContextConstantProjection k (Q.target a.val) (Q.source a.val)
        (f ⟨a.val, a.property.2.2⟩))
        (⟨b, a.property.1.symm, a.property.2.1.symm, hb⟩ :
          Q.FoundationRelationArrow (Q.target a.val) (Q.source a.val)) := by
  classical
  rw [noncutJacobianContextLeadingAggregationCoordinates]
  change (Finsupp.lapply a : (Q.FoundationRelationArrow (Q.target b) (Q.source b) →₀ k) →ₗ[k] k)
    (∑ a', Q.noncutJacobianContextTransposedLeadingCoordinates k a' b hb (f a')) = _
  rw [map_sum]
  dsimp only [Finsupp.lapply_apply]
  rw [Finset.sum_eq_single (⟨a.val, a.property.2.2⟩ : {a : Q.Arrow // Q.cut a = true})]
  · rw [noncutJacobianContextTransposedLeadingCoordinates,
      dif_pos ⟨a.property.1, a.property.2.1⟩]
    dsimp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Finsupp.lapply_apply]
    have he : (⟨a.val, a.property.1, a.property.2.1, a.property.2.2⟩ :
        Q.FoundationRelationArrow (Q.target b) (Q.source b)) = a := Subtype.ext rfl
    rw [he, Finsupp.single_eq_same]
  · intro a' _ hne
    rw [noncutJacobianContextTransposedLeadingCoordinates]
    split_ifs with he
    · dsimp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Finsupp.lapply_apply]
      apply Finsupp.single_eq_of_ne
      intro H
      apply hne
      exact Subtype.ext (congrArg Subtype.val H).symm
    · rfl
  · simp

theorem noncutJacobianContextLeadingAggregation_projection
    (b : Q.Arrow) (hb : Q.cut b = true)
    (f : ∀ a : {a : Q.Arrow // Q.cut a = true},
      Q.NoncutJacobianContextIndex (Q.target a.val) (Q.source a.val) →₀ k) :
    Q.pathArrowProjection k (Q.source b) (Q.target b)
      (∑ a : {a : Q.Arrow // Q.cut a = true},
        Q.noncutJacobianContextTransposedLinearMap k a b (f a)) =
      (Q.foundationCutArrowCoordinateEquiv k (Q.target b) (Q.source b) (Q.backward b hb)
        (Q.noncutJacobianContextLeadingAggregationCoordinates k b hb f)).val := by
  classical
  rw [map_sum, noncutJacobianContextLeadingAggregationCoordinates, map_sum]
  simp only [Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact Q.noncutJacobianContextTransposedLinearMap_projection k a b hb (f a)

end ASGinzburg.CutQuiver
