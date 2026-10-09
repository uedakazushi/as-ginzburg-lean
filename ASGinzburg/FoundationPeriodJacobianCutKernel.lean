import ASGinzburg.FoundationPeriodCutRelations
import ASGinzburg.UnrolledJacobianRelationShifts
import ASGinzburg.ArbitraryArrowKernelHeights

/-! The genuine cut-arrow Jacobian generators on every sheet are
in the actual AS period-transported presentation kernel. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem ASRegular.foundationPeriodCutJacobianRelation_eval_zero
    (hAS : A.ASRegular Q) (b : {a : Q.Arrow // Q.cut a=true}) (m : ℤ) :
    A.arrowPathLinearEvaluation Q (hAS.foundationPeriodIncomingElement A Q)
      (Q.target b.val,m) (Q.source b.val,m)
      (Q.unrolledCutJacobianRelation k (hAS.foundationPotential A Q) b m) = 0 := by
  let hx : Q.shift m (Q.target b.val,0)=(Q.target b.val,m) := by simp [CutQuiver.shift]
  let hy : Q.shift m (Q.source b.val,0)=(Q.source b.val,m) := by simp [CutQuiver.shift]
  let f := Q.unrolledSheetShiftLinearEquiv k m (Q.target b.val,0) (Q.source b.val,0)
    (hAS.foundationCutDerivativeUnroll A Q b)
  have heq : Finsupp.mapDomain (CutQuiver.UnrolledPath.endpointEquiv Q hx hy) f =
      Q.unrolledCutJacobianRelation k (hAS.foundationPotential A Q) b m := by
    apply Q.unrolledPathEraseLinearMap_injective k
    exact (Q.unrolledPathEraseLinearMap_sheet_transport k (Q.target b.val) (Q.source b.val)
      (m:=0+m) (n:=0+m) (m':=m) (n':=m) hx hy f).trans
      ((hAS.foundationCutDerivativeUnroll_period_erase A Q m b).trans
        (Q.unrolledCutJacobianRelation_erase k (hAS.foundationPotential A Q) b m).symm)
  rw [← heq]
  apply (A.arrowPathLinearEvaluation_transport_eq_zero_iff Q
    (hAS.foundationPeriodIncomingElement A Q) hx hy f).mpr
  exact hAS.foundationCutDerivativeUnroll_period_eval_zero A Q m b

theorem ASRegular.foundationPeriodJacobianRelation_cut_eval_zero
    (hAS : A.ASRegular Q) (a : Q.Arrow) (ha : Q.cut a=true) (m : ℤ) :
    A.arrowPathLinearEvaluation Q (hAS.foundationPeriodIncomingElement A Q)
      (Q.target a,m) (Q.source a,m+((1-Q.cutDegree a:ℕ):ℤ))
      (Q.unrolledJacobianRelation k a (hAS.foundationPotential A Q) m) = 0 := by
  have hy : (Q.source a,m+((1-Q.cutDegree a:ℕ):ℤ))=(Q.source a,m) := by
    simp [CutQuiver.cutDegree,ha]
  apply (A.arrowPathLinearEvaluation_transport_eq_zero_iff Q
    (hAS.foundationPeriodIncomingElement A Q) rfl hy _).mp
  exact hAS.foundationPeriodCutJacobianRelation_eval_zero A Q ⟨a,ha⟩ m

theorem ASRegular.foundationPeriodIntegerJacobianRelation_cut_mem_kernel
    (hAS : A.ASRegular Q) (a : Q.Arrow) (ha : Q.cut a=true) (m : ℤ) :
    Q.integerJacobianRelation k a (hAS.foundationPotential A Q) m ∈
      (A.arrowPathPresentation Q (hAS.foundationPeriodIncomingElement A Q)).kernel.hom
        (Q.height (Q.target a,m))
        (Q.height (Q.source a,m+((1-Q.cutDegree a:ℕ):ℤ))) := by
  apply (A.unrolledComponentHeightEquiv_mem_arrowPresentation_kernel_iff Q
    (hAS.foundationPeriodIncomingElement A Q) _ _ _).mpr
  exact hAS.foundationPeriodJacobianRelation_cut_eval_zero A Q a ha m

end ASGinzburg.ZAlgebra
