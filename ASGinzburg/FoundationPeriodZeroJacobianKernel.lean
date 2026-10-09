import ASGinzburg.ZeroCutJacobianEvaluation
import ASGinzburg.FoundationPeriodJacobianCutKernel
import ASGinzburg.FoundationPeriodZeroKernel
import ASGinzburg.UnrolledJacobianSheetShift

/-! On the original foundation, the actual periodic AS presentation
kernel equals the full Jacobian ideal of its foundation potential. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem ASRegular.foundationRelationLift_mem_Jacobian (hAS : A.ASRegular Q)
    (i j : Q.Vertex) (a : Q.FoundationRelationArrow i j) :
    (hAS.foundationRelationLift A Q i j a).val ∈
      (Q.unrolledJacobianIdeal k (hAS.foundationPotential A Q)).hom (i.val : ℤ) (j.val : ℤ) := by
  obtain ⟨a,hs,ht,hc⟩ := a
  subst i
  subst j
  let b : {a : Q.Arrow // Q.cut a=true} := ⟨a,hc⟩
  have h : hAS.foundationCutDerivativeUnroll A Q b ∈
      Q.unrolledJacobianLiftIdeal k (hAS.foundationPotential A Q)
        (Q.target a,0) (Q.source a,0) := by
    apply (Q.unrolledJacobianLiftIdeal_mem_iff_erase k (hAS.foundationPotential A Q) _).mpr
    change Q.unrolledPathEraseLinearMap k _ _ (hAS.foundationCutDerivativeUnroll A Q b) ∈ _
    have he : Q.unrolledPathEraseLinearMap k (Q.target a,0) (Q.source a,0)
        (hAS.foundationCutDerivativeUnroll A Q b) =
        Q.pathCyclicDerivative k a (hAS.foundationPotential A Q) :=
      Q.pathCutUnrollingEquiv_erase k (Q.target a) (Q.source a) 0 0
        ⟨Q.pathCyclicDerivative k a (hAS.foundationPotential A Q),by
          rw [hAS.foundationPotential_pathCyclicDerivative A Q b]
          exact hAS.cutPathRelation_cut A Q b⟩
    rw [he]
    exact Q.pathCyclicDerivative_mem_pathJacobianIdeal k (hAS.foundationPotential A Q) a
  change Q.unrolledComponentHeightEquiv k (Q.target a,0) (Q.source a,0)
    (hAS.foundationCutDerivativeUnroll A Q b) ∈
    (Q.unrolledJacobianIdeal k (hAS.foundationPotential A Q)).hom
      (Q.height (Q.target a,0)) (Q.height (Q.source a,0)) at h
  rw [hAS.foundationCutDerivativeUnroll_height A Q b] at h
  exact h

theorem ASRegular.foundationRelationIdeal_le_Jacobian (hAS : A.ASRegular Q)
    (i j : ℤ) :
    (hAS.foundationRelationIdeal A Q).hom i j ≤
      (Q.unrolledJacobianIdeal k (hAS.foundationPotential A Q)).hom i j := by
  apply LinearIdeal.generated_le
  intro i j f hf
  obtain ⟨x,y,hx,hy,a,rfl⟩ := hf
  subst i
  subst j
  exact hAS.foundationRelationLift_mem_Jacobian A Q x y a

theorem ASRegular.foundationPeriodPathKernel_zeroSheet_eq_Jacobian
    (hAS : A.ASRegular Q) (i j : Q.Vertex) :
    (A.arrowPathPresentation Q (hAS.foundationPeriodIncomingElement A Q)).kernel.hom
        (i.val : ℤ) (j.val : ℤ) =
      (Q.unrolledJacobianIdeal k (hAS.foundationPotential A Q)).hom (i.val : ℤ) (j.val : ℤ) := by
  apply le_antisymm
  · rw [hAS.foundationPeriodPathKernel_zeroSheet A Q i j]
    exact hAS.foundationRelationIdeal_le_Jacobian A Q _ _
  · intro f hf
    let g := (Q.unrolledComponentHeightEquiv k (i,0) (j,0)).symm f
    have hg : g ∈ Q.unrolledJacobianLiftIdeal k (hAS.foundationPotential A Q) (i,0) (j,0) := by
      change Q.unrolledComponentHeightEquiv k (i,0) (j,0) g ∈
        (Q.unrolledJacobianIdeal k (hAS.foundationPotential A Q)).hom
          (Q.height (i,0)) (Q.height (j,0))
      rwa [LinearEquiv.apply_symm_apply]
    have hz := A.arrowPathLinearEvaluation_zeroCutJacobianLift Q
      (hAS.foundationPeriodIncomingElement A Q) (hAS.foundationPotential A Q)
      (hAS.foundationPeriodJacobianRelation_cut_eval_zero A Q) (i,0) (j,0) rfl hg
    have hk := (A.unrolledComponentHeightEquiv_mem_arrowPresentation_kernel_iff Q
      (hAS.foundationPeriodIncomingElement A Q) (i,0) (j,0) g).mpr hz
    rwa [LinearEquiv.apply_symm_apply] at hk

end ASGinzburg.ZAlgebra
