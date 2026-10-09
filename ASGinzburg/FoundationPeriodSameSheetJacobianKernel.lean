import ASGinzburg.FoundationPeriodZeroJacobianKernel
import ASGinzburg.FoundationPeriodEvaluationCoherence

/-! The genuine full Jacobian kernel comparison holds on every
same-sheet component of the AS period-transported presentation. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem ASRegular.foundationPeriodPathLinearKernel_zeroSheet_eq_Jacobian
    (hAS : A.ASRegular Q) (i j : Q.Vertex) :
    LinearMap.ker (A.arrowPathLinearEvaluation Q (hAS.foundationPeriodIncomingElement A Q)
        (i,0) (j,0)) =
      Q.unrolledJacobianLiftIdeal k (hAS.foundationPotential A Q) (i,0) (j,0) := by
  ext f
  change A.arrowPathLinearEvaluation Q (hAS.foundationPeriodIncomingElement A Q)
      (i,0) (j,0) f=0 ↔
    Q.unrolledComponentHeightEquiv k (i,0) (j,0) f ∈
      (Q.unrolledJacobianIdeal k (hAS.foundationPotential A Q)).hom
        (Q.height (i,0)) (Q.height (j,0))
  rw [← A.unrolledComponentHeightEquiv_mem_arrowPresentation_kernel_iff Q
    (hAS.foundationPeriodIncomingElement A Q)]
  change Q.unrolledComponentHeightEquiv k (i,0) (j,0) f ∈
      (A.arrowPathPresentation Q (hAS.foundationPeriodIncomingElement A Q)).kernel.hom
        (i.val : ℤ) (j.val : ℤ) ↔
    Q.unrolledComponentHeightEquiv k (i,0) (j,0) f ∈
      (Q.unrolledJacobianIdeal k (hAS.foundationPotential A Q)).hom (i.val : ℤ) (j.val : ℤ)
  rw [hAS.foundationPeriodPathKernel_zeroSheet_eq_Jacobian A Q i j]

theorem ASRegular.foundationPeriodPathLinearKernel_shiftedZeroSheet_eq_Jacobian
    (hAS : A.ASRegular Q) (m : ℤ) (i j : Q.Vertex) :
    LinearMap.ker (A.arrowPathLinearEvaluation Q (hAS.foundationPeriodIncomingElement A Q)
        (Q.shift m (i,0)) (Q.shift m (j,0))) =
      Q.unrolledJacobianLiftIdeal k (hAS.foundationPotential A Q)
        (Q.shift m (i,0)) (Q.shift m (j,0)) := by
  rw [← hAS.foundationPeriodPathLinearEvaluation_integer_shift_kernel A Q m (i,0) (j,0),
    ← Q.unrolledSheetShiftLinearEquiv_Jacobian k (hAS.foundationPotential A Q) m (i,0) (j,0),
    hAS.foundationPeriodPathLinearKernel_zeroSheet_eq_Jacobian A Q i j]

theorem ASRegular.foundationPeriodPathLinearKernel_sameSheet_eq_Jacobian
    (hAS : A.ASRegular Q) (m : ℤ) (i j : Q.Vertex) :
    LinearMap.ker (A.arrowPathLinearEvaluation Q (hAS.foundationPeriodIncomingElement A Q)
        (i,m) (j,m)) =
      Q.unrolledJacobianLiftIdeal k (hAS.foundationPotential A Q) (i,m) (j,m) := by
  let P : ℤ → Prop := fun s =>
    LinearMap.ker (A.arrowPathLinearEvaluation Q (hAS.foundationPeriodIncomingElement A Q)
      (i,s) (j,s)) = Q.unrolledJacobianLiftIdeal k (hAS.foundationPotential A Q) (i,s) (j,s)
  have h : P (0+m) :=
    hAS.foundationPeriodPathLinearKernel_shiftedZeroSheet_eq_Jacobian A Q m i j
  rw [zero_add] at h
  exact h

end ASGinzburg.ZAlgebra
