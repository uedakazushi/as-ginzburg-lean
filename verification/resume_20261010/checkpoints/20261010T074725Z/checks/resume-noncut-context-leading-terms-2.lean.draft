import work.ASGinzburgDraft.NoncutJacobianContextTransposedFamily
import work.ASGinzburgDraft.NoncutJacobianContextConstantProjection
import work.ASGinzburgDraft.FoundationCutArrowCoordinates

/-! The actual length-one part of a transposed context is its constant
context coefficient, on the original source cut arrow. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem noncutJacobianContextTransposedTerm_projection_same_endpoints
    (a : {a : Q.Arrow // Q.cut a = true}) (b : Q.Arrow) (hb : Q.cut b = true)
    (hs : Q.source a.val = Q.source b) (ht : Q.target a.val = Q.target b)
    (c : Q.NoncutJacobianContextIndex (Q.target a.val) (Q.source a.val)) :
    Q.pathArrowProjection k (Q.source b) (Q.target b)
      (Q.noncutJacobianContextTransposedTerm k a b c) =
      Finsupp.single (Q.foundationCutArrowPath (Q.target b) (Q.source b)
        (⟨a.val, hs, ht, a.property⟩ : Q.FoundationRelationArrow (Q.target b) (Q.source b)))
        ((Q.noncutJacobianContextConstantProjection k (Q.target a.val) (Q.source a.val)
          (Finsupp.single c 1))
          (⟨b, hs.symm, ht.symm, hb⟩ : Q.FoundationRelationArrow (Q.target a.val) (Q.source a.val))) := by
  classical
  by_cases hc : c.1.val = b
  · rw [noncutJacobianContextTransposedTerm, dif_pos hc,
      pathArrowProjection_single, noncutJacobianContextConstantProjection_single]
    by_cases h0 : c.2.1.val.length = 0 ∧ c.2.2.val.length = 0
    · have hp := (Q.pathJacobianContextTranspose_length_one_iff a.val c.1.val
        c.2.1.val c.2.2.val).mpr h0
      have hw : (Q.pathJacobianContextTranspose a.val c.1.val c.2.1.val c.2.2.val).transport
          (congrArg Q.source hc) (congrArg Q.target hc) =
          Q.foundationCutArrowPath (Q.target b) (Q.source b) ⟨a.val, hs, ht, a.property⟩ := by
        apply Path.toList_injective
        simp only [Path.toList_transport, Q.pathJacobianContextTranspose_leading_word _ _ _ _ hp,
          foundationCutArrowPath, baseArrowPath, Path.toList, List.nil_append]
      have he : Q.noncutJacobianContextConstantArrow (Q.target a.val) (Q.source a.val)
          c h0.1 h0.2 = ⟨b, hs.symm, ht.symm, hb⟩ := Subtype.ext hc
      rw [dif_pos h0, he, Finsupp.single_eq_same, hw,
        foundationCutArrowPath_length, if_pos rfl]
    · have hp : (Q.pathJacobianContextTranspose a.val c.1.val c.2.1.val c.2.2.val).length ≠ 1 := by
        exact fun H => h0 ((Q.pathJacobianContextTranspose_length_one_iff _ _ _ _).mp H)
      simp only [Path.length_transport, if_neg hp, dif_neg h0, Finsupp.zero_apply, Finsupp.single_zero]
  · rw [noncutJacobianContextTransposedTerm, dif_neg hc, map_zero,
      noncutJacobianContextConstantProjection_single]
    split_ifs with h0
    · have he : Q.noncutJacobianContextConstantArrow (Q.target a.val) (Q.source a.val)
          c h0.1 h0.2 ≠ ⟨b, hs.symm, ht.symm, hb⟩ := by
        intro H
        exact hc (congrArg Subtype.val H)
      simp only [Finsupp.single_eq_of_ne' he, Finsupp.single_zero]
    · simp

theorem noncutJacobianContextTransposedTerm_projection_different_endpoints
    (a : {a : Q.Arrow // Q.cut a = true}) (b : Q.Arrow)
    (h : ¬ (Q.source a.val = Q.source b ∧ Q.target a.val = Q.target b))
    (c : Q.NoncutJacobianContextIndex (Q.target a.val) (Q.source a.val)) :
    Q.pathArrowProjection k (Q.source b) (Q.target b)
      (Q.noncutJacobianContextTransposedTerm k a b c) = 0 := by
  classical
  rw [noncutJacobianContextTransposedTerm]
  split_ifs with hc
  · rw [pathArrowProjection_single]
    have hp : (Q.pathJacobianContextTranspose a.val c.1.val c.2.1.val c.2.2.val).length ≠ 1 := by
      intro H
      have he := Q.pathJacobianContextTranspose_leading_endpoints _ _ _ _ H
      exact h ⟨he.1.trans (congrArg Q.source hc), he.2.trans (congrArg Q.target hc)⟩
    simp only [Path.length_transport, if_neg hp]
  · exact map_zero _

noncomputable def noncutJacobianContextTransposedLeadingCoordinates
    (a : {a : Q.Arrow // Q.cut a = true}) (b : Q.Arrow) (hb : Q.cut b = true) :
    (Q.NoncutJacobianContextIndex (Q.target a.val) (Q.source a.val) →₀ k) →ₗ[k]
      (Q.FoundationRelationArrow (Q.target b) (Q.source b) →₀ k) := by
  classical
  exact if h : Q.source a.val = Q.source b ∧ Q.target a.val = Q.target b then
    (Finsupp.lsingle (⟨a.val, h.1, h.2, a.property⟩ :
      Q.FoundationRelationArrow (Q.target b) (Q.source b))).comp
      ((Finsupp.lapply (⟨b, h.1.symm, h.2.symm, hb⟩ :
        Q.FoundationRelationArrow (Q.target a.val) (Q.source a.val))).comp
          (Q.noncutJacobianContextConstantProjection k (Q.target a.val) (Q.source a.val)))
  else 0

theorem noncutJacobianContextTransposedLinearMap_projection
    (a : {a : Q.Arrow // Q.cut a = true}) (b : Q.Arrow) (hb : Q.cut b = true)
    (f : Q.NoncutJacobianContextIndex (Q.target a.val) (Q.source a.val) →₀ k) :
    Q.pathArrowProjection k (Q.source b) (Q.target b)
      (Q.noncutJacobianContextTransposedLinearMap k a b f) =
      (Q.foundationCutArrowCoordinateEquiv k (Q.target b) (Q.source b) (Q.backward b hb)
        (Q.noncutJacobianContextTransposedLeadingCoordinates k a b hb f)).val := by
  classical
  let L := (Q.pathArrowProjection k (Q.source b) (Q.target b)).comp
    (Q.noncutJacobianContextTransposedLinearMap k a b)
  let R := (Q.pathArrowComponent k (Q.source b) (Q.target b)).subtype.comp
    ((Q.foundationCutArrowCoordinateEquiv k (Q.target b) (Q.source b) (Q.backward b hb)).toLinearMap.comp
      (Q.noncutJacobianContextTransposedLeadingCoordinates k a b hb))
  have hLR : L = R := by
    apply Finsupp.lhom_ext'
    intro c
    apply LinearMap.ext_ring
    dsimp only [L, R, LinearMap.comp_apply, Submodule.subtype_apply]
    rw [noncutJacobianContextTransposedLinearMap, Finsupp.lsingle_apply,
      Finsupp.linearCombination_single, one_smul]
    by_cases he : Q.source a.val = Q.source b ∧ Q.target a.val = Q.target b
    · rw [noncutJacobianContextTransposedLeadingCoordinates, dif_pos he]
      dsimp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Finsupp.lapply_apply]
      change Q.pathArrowProjection k (Q.source b) (Q.target b)
        (Q.noncutJacobianContextTransposedTerm k a b c) =
        (Q.foundationCutArrowCoordinateEquiv k (Q.target b) (Q.source b) (Q.backward b hb)
          (Finsupp.single ⟨a.val, he.1, he.2, a.property⟩
            ((Q.noncutJacobianContextConstantProjection k (Q.target a.val) (Q.source a.val)
              (Finsupp.single c 1)) ⟨b, he.1.symm, he.2.symm, hb⟩))).val
      rw [foundationCutArrowCoordinateEquiv_single]
      exact Q.noncutJacobianContextTransposedTerm_projection_same_endpoints k a b hb he.1 he.2 c
    · rw [noncutJacobianContextTransposedLeadingCoordinates, dif_neg he]
      simp only [LinearMap.zero_apply, map_zero, Submodule.coe_zero]
      exact Q.noncutJacobianContextTransposedTerm_projection_different_endpoints k a b he c
  exact LinearMap.congr_fun hLR f

end ASGinzburg.CutQuiver
