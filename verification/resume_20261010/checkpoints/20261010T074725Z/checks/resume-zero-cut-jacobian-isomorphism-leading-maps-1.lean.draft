import work.ASGinzburgDraft.ZeroCutJacobianIsomorphismArrowLifts
import work.ASGinzburgDraft.PathSubstitutionLeadingComposition

/-! Admissibility of the actual Jacobian kernels forces the chosen
foundation lifts to induce inverse maps on length-one arrow spaces. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]
variable {φ ψ : Q.Potential k}
variable (F : ZAlgebra.Isomorphism (Q.unrolledJacobianZAlgebra k φ)
  (Q.unrolledJacobianZAlgebra k ψ))

theorem zeroCutIsomorphismSubstitution_comp_difference_mem_length (i j : Q.Vertex)
    (f : Q.pathCutComponent k i j 0) :
    (Q.pathCutSubstitution k (Q.zeroCutIsomorphismArrowReplacement k F.symm)
      (Q.zeroCutIsomorphismArrowReplacement_mem_cut k F.symm) i j 0
        (Q.pathCutSubstitution k (Q.zeroCutIsomorphismArrowReplacement k F)
          (Q.zeroCutIsomorphismArrowReplacement_mem_cut k F) i j 0 f)).val - f.val ∈
      Q.pathLengthFiltration k 2 i j := by
  apply Q.zeroCutJacobianComponentProjection_kernel_length k φ i j
    (Q.pathCutSubstitution k (Q.zeroCutIsomorphismArrowReplacement k F.symm)
      (Q.zeroCutIsomorphismArrowReplacement_mem_cut k F.symm) i j 0
        (Q.pathCutSubstitution k (Q.zeroCutIsomorphismArrowReplacement k F)
          (Q.zeroCutIsomorphismArrowReplacement_mem_cut k F) i j 0 f) - f)
  rw [map_sub,Q.zeroCutIsomorphismSubstitution_projection,
    Q.zeroCutIsomorphismSubstitution_projection]
  change (F.map (i.val : ℤ) (j.val : ℤ)).symm
    (F.map _ _ (Q.zeroCutJacobianComponentProjection k φ i j f)) -
      Q.zeroCutJacobianComponentProjection k φ i j f = 0
  rw [LinearEquiv.symm_apply_apply,sub_self]

theorem zeroCutIsomorphismSubstitution_leading_inverse_arrow (a : Q.Arrow) :
    Q.pathArrowProjection k (Q.source a) (Q.target a)
      (Q.pathArrowSubstitutionComponent k (Q.zeroCutIsomorphismArrowReplacement k F.symm)
        (Q.source a) (Q.target a) (Q.zeroCutIsomorphismArrowReplacement k F a)) =
        Q.pathIdentityArrowReplacement k a := by
  cases ha : Q.cut a
  · have H := Q.zeroCutIsomorphismSubstitution_comp_difference_mem_length k F
      (Q.source a) (Q.target a) (Q.zeroCutArrowElement k a ha)
    have Harrow : Q.pathArrowSubstitutionComponent k (Q.zeroCutIsomorphismArrowReplacement k F)
        (Q.source a) (Q.target a) (Q.pathIdentityArrowReplacement k a) =
          Q.zeroCutIsomorphismArrowReplacement k F a := by
      rw [pathIdentityArrowReplacement,Q.pathArrowSubstitution_arrow]
    change Q.pathArrowSubstitutionComponent k (Q.zeroCutIsomorphismArrowReplacement k F.symm)
      (Q.source a) (Q.target a)
        (Q.pathArrowSubstitutionComponent k (Q.zeroCutIsomorphismArrowReplacement k F)
          (Q.source a) (Q.target a) (Q.pathIdentityArrowReplacement k a)) -
        Q.pathIdentityArrowReplacement k a ∈ _ at H
    rw [Harrow] at H
    have Hzero := Q.pathArrowProjection_eq_zero_of_length_two k _ H
    rw [map_sub] at Hzero
    have Hid : Q.pathArrowProjection k (Q.source a) (Q.target a)
        (Q.pathIdentityArrowReplacement k a) = Q.pathIdentityArrowReplacement k a :=
      Q.pathArrowProjection_on_arrow k _ _ (Q.pathArrowBasisElement k a)
    rw [Hid] at Hzero
    exact sub_eq_zero.mp Hzero
  · rw [Q.zeroCutIsomorphismArrowReplacement_cut k F a ha,
      pathIdentityArrowReplacement,Q.pathArrowSubstitution_arrow,
      Q.zeroCutIsomorphismArrowReplacement_cut k F.symm a ha]
    exact Q.pathArrowProjection_on_arrow k _ _ (Q.pathArrowBasisElement k a)

theorem zeroCutIsomorphismSubstitution_leading_bijective (i j : Q.Vertex) :
    Function.Bijective
      (Q.pathSubstitutionArrowLinearMap k (Q.zeroCutIsomorphismArrowReplacement k F) i j) := by
  have Hleft := Q.pathSubstitutionArrowLinearMap_inverse_of_arrow k
    (Q.zeroCutIsomorphismArrowReplacement k F) (Q.zeroCutIsomorphismArrowReplacement k F.symm)
    (Q.zeroCutIsomorphismSubstitution_leading_inverse_arrow k F) i j
  have Hright := Q.pathSubstitutionArrowLinearMap_inverse_of_arrow k
    (Q.zeroCutIsomorphismArrowReplacement k F.symm)
    (Q.zeroCutIsomorphismArrowReplacement k F.symm.symm)
    (Q.zeroCutIsomorphismSubstitution_leading_inverse_arrow k F.symm) i j
  refine ⟨Function.LeftInverse.injective Hleft,?_⟩
  intro y
  refine ⟨Q.pathSubstitutionArrowLinearMap k (Q.zeroCutIsomorphismArrowReplacement k F.symm) i j y,?_⟩
  exact Hright y

end ASGinzburg.CutQuiver
