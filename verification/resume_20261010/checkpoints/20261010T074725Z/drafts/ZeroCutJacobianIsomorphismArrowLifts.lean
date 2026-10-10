import work.ASGinzburgDraft.ZeroCutPathSubstitutionIntertwining

/-! A genuine vertex-fixed Jacobian Z-algebra isomorphism supplies actual
noncut homogeneous arrow lifts. The cut arrows are kept fixed, and the
free substitution intertwines the entire original zero-sheet foundation. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]
variable {φ ψ : Q.Potential k}
variable (F : ZAlgebra.Isomorphism (Q.unrolledJacobianZAlgebra k φ)
  (Q.unrolledJacobianZAlgebra k ψ))

noncomputable def zeroCutIsomorphismArrowLift (a : Q.Arrow) (ha : Q.cut a = false) :
    Q.pathCutComponent k (Q.source a) (Q.target a) 0 :=
  (Q.zeroCutJacobianComponentProjection_surjective k ψ (Q.source a) (Q.target a)
    (F.map _ _ (Q.zeroCutJacobianComponentProjection k φ _ _
      (Q.zeroCutArrowElement k a ha)))).choose

theorem zeroCutIsomorphismArrowLift_projection (a : Q.Arrow) (ha : Q.cut a = false) :
    Q.zeroCutJacobianComponentProjection k ψ _ _ (Q.zeroCutIsomorphismArrowLift k F a ha) =
      F.map _ _ (Q.zeroCutJacobianComponentProjection k φ _ _
        (Q.zeroCutArrowElement k a ha)) :=
  (Q.zeroCutJacobianComponentProjection_surjective k ψ (Q.source a) (Q.target a)
    (F.map _ _ (Q.zeroCutJacobianComponentProjection k φ _ _
      (Q.zeroCutArrowElement k a ha)))).choose_spec

noncomputable def zeroCutIsomorphismArrowReplacement : Q.PathArrowReplacement k :=
  fun a => if ha : Q.cut a = false then (Q.zeroCutIsomorphismArrowLift k F a ha).val
    else Q.pathIdentityArrowReplacement k a

theorem zeroCutIsomorphismArrowReplacement_mem_cut (a : Q.Arrow) :
    Q.zeroCutIsomorphismArrowReplacement k F a ∈
      Q.pathCutComponent k (Q.source a) (Q.target a) (Q.cutDegree a : ℤ) := by
  classical
  by_cases ha : Q.cut a = false
  · simp only [zeroCutIsomorphismArrowReplacement,dif_pos ha,Q.cutDegree_false ha,Nat.cast_zero]
    exact (Q.zeroCutIsomorphismArrowLift k F a ha).property
  · rw [zeroCutIsomorphismArrowReplacement,dif_neg ha]
    exact Finsupp.single_mem_supported k 1 (by simp [Path.cutDegree])

theorem zeroCutIsomorphismArrowReplacement_cut (a : Q.Arrow) (ha : Q.cut a = true) :
    Q.zeroCutIsomorphismArrowReplacement k F a = Q.pathIdentityArrowReplacement k a := by
  simp [zeroCutIsomorphismArrowReplacement,ha]

theorem zeroCutIsomorphismArrowReplacement_projection (a : Q.Arrow) (ha : Q.cut a = false) :
    Q.zeroCutJacobianComponentProjection k ψ (Q.source a) (Q.target a)
      (Q.pathCutSubstitution k (Q.zeroCutIsomorphismArrowReplacement k F)
        (Q.zeroCutIsomorphismArrowReplacement_mem_cut k F) _ _ 0 (Q.zeroCutArrowElement k a ha)) =
      F.map _ _ (Q.zeroCutJacobianComponentProjection k φ _ _ (Q.zeroCutArrowElement k a ha)) := by
  have H : Q.pathCutSubstitution k (Q.zeroCutIsomorphismArrowReplacement k F)
      (Q.zeroCutIsomorphismArrowReplacement_mem_cut k F) _ _ 0 (Q.zeroCutArrowElement k a ha) =
        Q.zeroCutIsomorphismArrowLift k F a ha := by
    apply Subtype.ext
    change Q.pathArrowSubstitutionComponent k (Q.zeroCutIsomorphismArrowReplacement k F) _ _
      (Q.pathIdentityArrowReplacement k a) = _
    rw [pathIdentityArrowReplacement,Q.pathArrowSubstitution_arrow]
    simp only [zeroCutIsomorphismArrowReplacement,dif_pos ha]
  rw [H]
  exact Q.zeroCutIsomorphismArrowLift_projection k F a ha

theorem zeroCutIsomorphismSubstitution_projection (i j : Q.Vertex)
    (f : Q.pathCutComponent k i j 0) :
    Q.zeroCutJacobianComponentProjection k ψ i j
      (Q.pathCutSubstitution k (Q.zeroCutIsomorphismArrowReplacement k F)
        (Q.zeroCutIsomorphismArrowReplacement_mem_cut k F) i j 0 f) =
      F.map _ _ (Q.zeroCutJacobianComponentProjection k φ i j f) :=
  Q.zeroCutPathSubstitution_projection k F (Q.zeroCutIsomorphismArrowReplacement k F)
    (Q.zeroCutIsomorphismArrowReplacement_mem_cut k F)
    (Q.zeroCutIsomorphismArrowReplacement_projection k F) i j f

end ASGinzburg.CutQuiver
