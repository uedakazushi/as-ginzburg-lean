import ASGinzburg.FoundationPeriodIntegerCoherence
import ASGinzburg.PeriodicArrowIntegerLinearKernels

/-! The original AS condition discharges the coherence hypothesis for
its concrete foundation-transported arrow family. Therefore its true
presentation kernels are periodic on every integer sheet. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem ASRegular.foundationPeriodIncomingElement_periodCoherent (hAS : A.ASRegular Q) :
    (hAS.foundationPeriodIncomingElement A Q).PeriodCoherent A Q (hAS.periodIso A Q) := by
  rintro ⟨j,m⟩ a
  exact hAS.foundationPeriodIncomingElement_int_succ A Q m j a

theorem ASRegular.foundationPeriodPathEvaluation_shift (hAS : A.ASRegular Q)
    {x y : Q.LiftVertex} (p : Q.UnrolledPath x y) :
    A.arrowPathEvaluation Q (hAS.foundationPeriodIncomingElement A Q) (p.shift 1) =
      (hAS.periodIso A Q).liftedStepMap A Q x y
        (A.arrowPathEvaluation Q (hAS.foundationPeriodIncomingElement A Q) p) :=
  A.arrowPathEvaluation_shift Q (hAS.foundationPeriodIncomingElement A Q)
    (hAS.periodIso A Q) (hAS.foundationPeriodIncomingElement_periodCoherent A Q) p

theorem ASRegular.foundationPeriodPathLinearEvaluation_shift (hAS : A.ASRegular Q)
    {x y : Q.LiftVertex} (f : Q.UnrolledPathComponent k x y) :
    A.arrowPathLinearEvaluation Q (hAS.foundationPeriodIncomingElement A Q)
      (Q.shift 1 x) (Q.shift 1 y) (Q.unrolledSheetShiftLinearEquiv k 1 x y f) =
      (hAS.periodIso A Q).liftedStepMap A Q x y
        (A.arrowPathLinearEvaluation Q (hAS.foundationPeriodIncomingElement A Q) x y f) :=
  A.arrowPathLinearEvaluation_shift Q (hAS.foundationPeriodIncomingElement A Q)
    (hAS.periodIso A Q) (hAS.foundationPeriodIncomingElement_periodCoherent A Q) f

theorem ASRegular.foundationPeriodPathLinearEvaluation_integer_shift_eq_zero_iff
    (hAS : A.ASRegular Q) (r : ℤ) {x y : Q.LiftVertex}
    (f : Q.UnrolledPathComponent k x y) :
    A.arrowPathLinearEvaluation Q (hAS.foundationPeriodIncomingElement A Q)
      (Q.shift r x) (Q.shift r y) (Q.unrolledSheetShiftLinearEquiv k r x y f) = 0 ↔
      A.arrowPathLinearEvaluation Q (hAS.foundationPeriodIncomingElement A Q) x y f = 0 :=
  A.arrowPathLinearEvaluation_integer_shift_eq_zero_iff Q (hAS.foundationPeriodIncomingElement A Q)
    (hAS.periodIso A Q) (hAS.foundationPeriodIncomingElement_periodCoherent A Q) r f

theorem ASRegular.foundationPeriodPathLinearEvaluation_integer_shift_kernel
    (hAS : A.ASRegular Q) (r : ℤ) (x y : Q.LiftVertex) :
    Submodule.map (Q.unrolledSheetShiftLinearEquiv k r x y).toLinearMap
      (LinearMap.ker (A.arrowPathLinearEvaluation Q (hAS.foundationPeriodIncomingElement A Q) x y)) =
      LinearMap.ker (A.arrowPathLinearEvaluation Q (hAS.foundationPeriodIncomingElement A Q)
        (Q.shift r x) (Q.shift r y)) :=
  A.arrowPathLinearEvaluation_integer_shift_kernel Q (hAS.foundationPeriodIncomingElement A Q)
    (hAS.periodIso A Q) (hAS.foundationPeriodIncomingElement_periodCoherent A Q) r x y

end ASGinzburg.ZAlgebra
