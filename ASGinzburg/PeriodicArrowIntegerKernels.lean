import ASGinzburg.PeriodicArrowLinearKernel
import ASGinzburg.UnrolledPathShiftArithmetic

/-! Evaluation of a finite unrolled path is zero on one sheet
exactly when it is zero after any integer sheet shift. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)
variable (G : A.IncomingElementFamily Q) (E : A.PeriodIso Q.vertices)
variable (hG : G.PeriodCoherent A Q E)
include E hG

theorem arrowPathEvaluation_one_shift_eq_zero_iff {x y : Q.LiftVertex}
    (p : Q.UnrolledPath x y) :
    A.arrowPathEvaluation Q G (p.shift 1) = 0 ↔ A.arrowPathEvaluation Q G p = 0 := by
  rw [A.arrowPathEvaluation_shift Q G E hG]
  exact (E.liftedStepMap A Q x y).map_eq_zero_iff

omit E hG in
theorem arrowPathEvaluation_transport_eq_zero_iff {x y x' y' : Q.LiftVertex}
    (hx : x=x') (hy : y=y') (p : Q.UnrolledPath x y) :
    A.arrowPathEvaluation Q G (p.transport hx hy) = 0 ↔
      A.arrowPathEvaluation Q G p = 0 := by
  rw [A.arrowPathEvaluation_transport Q G]
  exact (A.homTransport _ _ _ _ (congrArg Q.height hx) (congrArg Q.height hy)).map_eq_zero_iff

omit E hG in
theorem arrowPathEvaluation_shift_add_eq_zero_iff (r s : ℤ) {x y : Q.LiftVertex}
    (p : Q.UnrolledPath x y) :
    A.arrowPathEvaluation Q G ((p.shift r).shift s) = 0 ↔
      A.arrowPathEvaluation Q G (p.shift (r+s)) = 0 := by
  rw [CutQuiver.UnrolledPath.shift_add]
  exact A.arrowPathEvaluation_transport_eq_zero_iff Q G _ _ _

theorem arrowPathEvaluation_shift_step_eq_zero_iff (r : ℤ) {x y : Q.LiftVertex}
    (p : Q.UnrolledPath x y) :
    A.arrowPathEvaluation Q G (p.shift (r+1)) = 0 ↔
      A.arrowPathEvaluation Q G (p.shift r) = 0 :=
  (A.arrowPathEvaluation_shift_add_eq_zero_iff Q G r 1 p).symm.trans
    (A.arrowPathEvaluation_one_shift_eq_zero_iff Q G E hG (p.shift r))

theorem arrowPathEvaluation_integer_shift_eq_zero_iff (r : ℤ) {x y : Q.LiftVertex}
    (p : Q.UnrolledPath x y) :
    A.arrowPathEvaluation Q G (p.shift r) = 0 ↔ A.arrowPathEvaluation Q G p = 0 := by
  induction r using Int.induction_on with
  | zero =>
    rw [CutQuiver.UnrolledPath.shift_zero]
    exact A.arrowPathEvaluation_transport_eq_zero_iff Q G _ _ _
  | succ n ih =>
    exact (A.arrowPathEvaluation_shift_step_eq_zero_iff Q G E hG n p).trans ih
  | pred n ih =>
    let P : ℤ → Prop := fun s => A.arrowPathEvaluation Q G (p.shift s) = 0
    have step : P ((-(n : ℤ)-1)+1) ↔ P (-(n : ℤ)-1) :=
      A.arrowPathEvaluation_shift_step_eq_zero_iff Q G E hG (-(n : ℤ)-1) p
    rw [sub_add_cancel] at step
    exact step.symm.trans ih

end ASGinzburg.ZAlgebra
