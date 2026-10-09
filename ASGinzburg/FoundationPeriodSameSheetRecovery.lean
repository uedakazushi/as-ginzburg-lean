import ASGinzburg.FoundationPeriodSameSheetJacobianKernel
import ASGinzburg.JacobianUnrollingQuotient

/-! Actual same-sheet components of the candidate Jacobian algebra
recover the original AS algebra components, with their genuine products. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def ASRegular.foundationPeriodSameSheetRawEquiv
    (hAS : A.ASRegular Q) (m : ℤ) (i j : Q.Vertex) :
    (Q.UnrolledPathComponent k (i,m) (j,m) ⧸
      Q.unrolledJacobianLiftIdeal k (hAS.foundationPotential A Q) (i,m) (j,m)) ≃ₗ[k]
      A.Hom (Q.height (i,m)) (Q.height (j,m)) :=
  (Submodule.quotEquivOfEq _ _
    (hAS.foundationPeriodPathLinearKernel_sameSheet_eq_Jacobian A Q m i j).symm).trans
      ((A.arrowPathLinearEvaluation Q (hAS.foundationPeriodIncomingElement A Q) (i,m) (j,m)).quotKerEquivOfSurjective
        (hAS.foundationPeriodPathLinearEvaluation_surjective A Q (i,m) (j,m)))

theorem ASRegular.foundationPeriodSameSheetRawEquiv_apply_mk
    (hAS : A.ASRegular Q) (m : ℤ) (i j : Q.Vertex)
    (f : Q.UnrolledPathComponent k (i,m) (j,m)) :
    hAS.foundationPeriodSameSheetRawEquiv A Q m i j (Submodule.Quotient.mk f) =
      A.arrowPathLinearEvaluation Q (hAS.foundationPeriodIncomingElement A Q) (i,m) (j,m) f := by
  unfold foundationPeriodSameSheetRawEquiv
  rw [LinearEquiv.trans_apply,Submodule.quotEquivOfEq_mk]
  rfl

noncomputable def ASRegular.foundationPeriodSameSheetEquiv
    (hAS : A.ASRegular Q) (m : ℤ) (i j : Q.Vertex) :
    (Q.unrolledJacobianZAlgebra k (hAS.foundationPotential A Q)).Hom
      (Q.height (i,m)) (Q.height (j,m)) ≃ₗ[k]
      A.Hom (Q.height (i,m)) (Q.height (j,m)) :=
  (Q.unrolledJacobianLiftQuotientHeightEquiv k (hAS.foundationPotential A Q) (i,m) (j,m)).symm.trans
    (hAS.foundationPeriodSameSheetRawEquiv A Q m i j)

theorem ASRegular.foundationPeriodSameSheetEquiv_apply_mk
    (hAS : A.ASRegular Q) (m : ℤ) (i j : Q.Vertex)
    (f : Q.UnrolledPathComponent k (i,m) (j,m)) :
    hAS.foundationPeriodSameSheetEquiv A Q m i j
      (Submodule.Quotient.mk (Q.unrolledComponentHeightEquiv k (i,m) (j,m) f)) =
      A.arrowPathLinearEvaluation Q (hAS.foundationPeriodIncomingElement A Q) (i,m) (j,m) f := by
  change hAS.foundationPeriodSameSheetRawEquiv A Q m i j
    ((Q.unrolledJacobianLiftQuotientHeightEquiv k (hAS.foundationPotential A Q) (i,m) (j,m)).symm
      ((Q.unrolledJacobianLiftQuotientHeightEquiv k (hAS.foundationPotential A Q) (i,m) (j,m))
        (Submodule.Quotient.mk f))) = _
  rw [LinearEquiv.symm_apply_apply,hAS.foundationPeriodSameSheetRawEquiv_apply_mk A Q]

theorem ASRegular.foundationPeriodSameSheetEquiv_comp
    (hAS : A.ASRegular Q) (m : ℤ) (i j l : Q.Vertex)
    (f : (Q.unrolledJacobianZAlgebra k (hAS.foundationPotential A Q)).Hom
      (Q.height (i,m)) (Q.height (j,m)))
    (g : (Q.unrolledJacobianZAlgebra k (hAS.foundationPotential A Q)).Hom
      (Q.height (j,m)) (Q.height (l,m))) :
    hAS.foundationPeriodSameSheetEquiv A Q m i l
        ((Q.unrolledJacobianZAlgebra k (hAS.foundationPotential A Q)).comp g f) =
      A.comp (hAS.foundationPeriodSameSheetEquiv A Q m j l g)
        (hAS.foundationPeriodSameSheetEquiv A Q m i j f) := by
  obtain ⟨f,rfl⟩ := (Q.unrolledJacobianLiftQuotientHeightEquiv k
    (hAS.foundationPotential A Q) (i,m) (j,m)).surjective f
  obtain ⟨f,rfl⟩ := (Q.unrolledJacobianLiftIdeal k (hAS.foundationPotential A Q) (i,m) (j,m)).mkQ_surjective f
  obtain ⟨g,rfl⟩ := (Q.unrolledJacobianLiftQuotientHeightEquiv k
    (hAS.foundationPotential A Q) (j,m) (l,m)).surjective g
  obtain ⟨g,rfl⟩ := (Q.unrolledJacobianLiftIdeal k (hAS.foundationPotential A Q) (j,m) (l,m)).mkQ_surjective g
  change hAS.foundationPeriodSameSheetEquiv A Q m i l
      (Submodule.Quotient.mk ((Q.unrolledPathZAlgebra k).comp
        (Q.unrolledComponentHeightEquiv k (j,m) (l,m) g)
        (Q.unrolledComponentHeightEquiv k (i,m) (j,m) f))) =
    A.comp (hAS.foundationPeriodSameSheetEquiv A Q m j l
      (Submodule.Quotient.mk (Q.unrolledComponentHeightEquiv k (j,m) (l,m) g)))
      (hAS.foundationPeriodSameSheetEquiv A Q m i j
        (Submodule.Quotient.mk (Q.unrolledComponentHeightEquiv k (i,m) (j,m) f)))
  rw [← Q.unrolledComponentHeightEquiv_comp k,
    hAS.foundationPeriodSameSheetEquiv_apply_mk A Q,
    hAS.foundationPeriodSameSheetEquiv_apply_mk A Q,
    hAS.foundationPeriodSameSheetEquiv_apply_mk A Q]
  exact A.arrowPathLinearEvaluation_comp Q (hAS.foundationPeriodIncomingElement A Q) f g

theorem ASRegular.foundationPeriodSameSheetEquiv_id
    (hAS : A.ASRegular Q) (m : ℤ) (i : Q.Vertex) :
    hAS.foundationPeriodSameSheetEquiv A Q m i i
      ((Q.unrolledJacobianZAlgebra k (hAS.foundationPotential A Q)).id (Q.height (i,m))) =
      A.id (Q.height (i,m)) := by
  have hid : Q.unrolledComponentHeightEquiv k (i,m) (i,m) (Q.unrolledPathId k (i,m)) =
      (Q.unrolledPathZAlgebra k).id (Q.height (i,m)) := by
    change Finsupp.mapDomain (Q.unrolledPathHeightEquiv (i,m) (i,m))
      (Finsupp.single (CutQuiver.UnrolledPath.nil (i,m)) (1:k)) =
        Finsupp.single (CutQuiver.UnrolledPath.nil (Q.heightEquiv.symm (Q.height (i,m)))) (1:k)
    rw [Finsupp.mapDomain_single]
    exact congrArg (fun p => Finsupp.single p (1:k))
      (Q.unrolledPathHeightEquiv (i,m) (i,m) (CutQuiver.UnrolledPath.nil (i,m))).diagonal_eq_nil
  change hAS.foundationPeriodSameSheetEquiv A Q m i i
    (Submodule.Quotient.mk ((Q.unrolledPathZAlgebra k).id (Q.height (i,m)))) = _
  rw [← hid,hAS.foundationPeriodSameSheetEquiv_apply_mk A Q]
  exact A.arrowPathLinearEvaluation_id Q (hAS.foundationPeriodIncomingElement A Q) (i,m)

end ASGinzburg.ZAlgebra
