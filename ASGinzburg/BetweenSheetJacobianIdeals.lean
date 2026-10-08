import ASGinzburg.UnrolledJacobianContexts
import ASGinzburg.PathJacobianGrading

/-! The genuine homogeneous Jacobian ideal is carried into the genuine
unrolled relation ideal; with erasure, this gives equality of the ideals. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def betweenSheetProjectionMap (u v : Q.LiftVertex) :
    Q.PathComponent k u.1 v.1 →ₗ[k] Q.UnrolledPathComponent k u v :=
  (Q.betweenSheetLinearEquiv k u v).toLinearMap.comp
    ((Q.pathCutProjection k u.1 v.1 (v.2-u.2)).codRestrict _
      (Q.pathCutProjection_mem k (v.2-u.2)))

theorem betweenSheetProjectionMap_on_cut (u v : Q.LiftVertex)
    {f : Q.PathComponent k u.1 v.1} (hf : f ∈ Q.pathCutComponent k u.1 v.1 (v.2-u.2)) :
    Q.betweenSheetProjectionMap k u v f=Q.betweenSheetLinearEquiv k u v ⟨f,hf⟩ := by
  change Q.betweenSheetLinearEquiv k u v
    ⟨Q.pathCutProjection k u.1 v.1 (v.2-u.2) f,_⟩=_
  apply congrArg (Q.betweenSheetLinearEquiv k u v)
  apply Subtype.ext
  exact (Q.pathCutProjection_on_cut k (v.2-u.2) (v.2-u.2) hf).trans (if_pos rfl)

theorem betweenSheetProjectionMap_on_other_cut (u v : Q.LiftVertex) {c : ℤ}
    {f : Q.PathComponent k u.1 v.1} (hf : f ∈ Q.pathCutComponent k u.1 v.1 c)
    (hc : c≠v.2-u.2) : Q.betweenSheetProjectionMap k u v f=0 := by
  change Q.betweenSheetLinearEquiv k u v ⟨Q.pathCutProjection k u.1 v.1 (v.2-u.2) f,_⟩=0
  rw [←(Q.betweenSheetLinearEquiv k u v).map_zero]
  apply congrArg (Q.betweenSheetLinearEquiv k u v)
  apply Subtype.ext
  exact (Q.pathCutProjection_on_cut k (v.2-u.2) c hf).trans (if_neg hc)

theorem betweenSheetProjectionMap_mem_liftIdeal (φ : Q.Potential k) (u v : Q.LiftVertex)
    {f : Q.PathComponent k u.1 v.1} (hf : f ∈ (Q.pathJacobianIdeal k φ).hom u.1 v.1) :
    Q.betweenSheetProjectionMap k u v f ∈ Q.unrolledJacobianLiftIdeal k φ u v := by
  rw [Q.pathJacobianIdeal_eq_contextSpan] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a,l,r,rfl⟩ := hx
    by_cases hd : (Q.pathJacobianContextDegree a l r:ℤ)=v.2-u.2
    · have hc : Q.pathComp k (Finsupp.single r 1)
          (Q.pathComp k (Q.pathCyclicDerivative k a φ) (Finsupp.single l 1)) ∈
            Q.pathCutComponent k u.1 v.1 (v.2-u.2) := by
        rw [←hd]
        exact Q.pathJacobianContext_mem_cut k φ a l r
      rw [Q.betweenSheetProjectionMap_on_cut k u v hc]
      exact Q.unrolledJacobianContext_mem_liftIdeal k φ u v a l r hd
    · rw [Q.betweenSheetProjectionMap_on_other_cut k u v
        (Q.pathJacobianContext_mem_cut k φ a l r) hd]
      exact Submodule.zero_mem _
  | zero => simp
  | add f g hf hg ihf ihg => simpa only [map_add] using Submodule.add_mem _ ihf ihg
  | smul a f hf ih => simpa only [map_smul] using Submodule.smul_mem _ a ih

theorem betweenSheetJacobianIdeal_map (φ : Q.Potential k) (u v : Q.LiftVertex) :
    (Q.pathJacobianCutIdeal k φ u.1 v.1 (v.2-u.2)).map
      (Q.betweenSheetLinearEquiv k u v).toLinearMap=Q.unrolledJacobianLiftIdeal k φ u v := by
  apply Submodule.ext
  intro f
  constructor
  · rintro ⟨x,hx,rfl⟩
    have h := Q.betweenSheetProjectionMap_mem_liftIdeal k φ u v hx
    change Q.betweenSheetProjectionMap k u v x.val ∈ Q.unrolledJacobianLiftIdeal k φ u v at h
    rwa [Q.betweenSheetProjectionMap_on_cut k u v x.property] at h
  · intro hf
    refine ⟨(Q.betweenSheetLinearEquiv k u v).symm f,?_,
      (Q.betweenSheetLinearEquiv k u v).apply_symm_apply f⟩
    change ((Q.betweenSheetLinearEquiv k u v).symm f).val ∈
      (Q.pathJacobianIdeal k φ).hom u.1 v.1
    rw [Q.betweenSheetLinearEquiv_symm_coe]
    exact Q.unrolledJacobianLiftIdeal_erase k φ hf

end ASGinzburg.CutQuiver
