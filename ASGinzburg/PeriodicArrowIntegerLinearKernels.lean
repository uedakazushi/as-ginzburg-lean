import ASGinzburg.PeriodicArrowIntegerKernels
import ASGinzburg.UnrolledLinearShiftArithmetic

/-! Every integer sheet shift preserves the actual evaluation kernel
of all finite linear combinations, rather than only of individual paths. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)
variable (G : A.IncomingElementFamily Q) (E : A.PeriodIso Q.vertices)
variable (hG : G.PeriodCoherent A Q E)
include E hG

omit E hG in
theorem arrowPathLinearEvaluation_transport {x y x' y' : Q.LiftVertex}
    (hx : x=x') (hy : y=y') (f : Q.UnrolledPathComponent k x y) :
    A.arrowPathLinearEvaluation Q G x' y'
      (Finsupp.mapDomain (CutQuiver.UnrolledPath.endpointEquiv Q hx hy) f) =
      A.homTransport (Q.height x) (Q.height y) (Q.height x') (Q.height y')
        (congrArg Q.height hx) (congrArg Q.height hy)
        (A.arrowPathLinearEvaluation Q G x y f) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [Finsupp.mapDomain_add, map_add, hf, hg]
  | single p c =>
    simp only [Finsupp.mapDomain_single, arrowPathLinearEvaluation_single, map_smul]
    exact congrArg (fun t => c • t) (A.arrowPathEvaluation_transport Q G hx hy p)

omit E hG in
theorem arrowPathLinearEvaluation_transport_eq_zero_iff {x y x' y' : Q.LiftVertex}
    (hx : x=x') (hy : y=y') (f : Q.UnrolledPathComponent k x y) :
    A.arrowPathLinearEvaluation Q G x' y'
      (Finsupp.mapDomain (CutQuiver.UnrolledPath.endpointEquiv Q hx hy) f) = 0 ↔
      A.arrowPathLinearEvaluation Q G x y f = 0 := by
  rw [A.arrowPathLinearEvaluation_transport Q G]
  exact (A.homTransport _ _ _ _ (congrArg Q.height hx) (congrArg Q.height hy)).map_eq_zero_iff

omit E hG in
theorem arrowPathLinearEvaluation_shift_add_eq_zero_iff (r s : ℤ)
    {x y : Q.LiftVertex} (f : Q.UnrolledPathComponent k x y) :
    A.arrowPathLinearEvaluation Q G (Q.shift s (Q.shift r x)) (Q.shift s (Q.shift r y))
      (Q.unrolledSheetShiftLinearEquiv k s (Q.shift r x) (Q.shift r y)
        (Q.unrolledSheetShiftLinearEquiv k r x y f)) = 0 ↔
      A.arrowPathLinearEvaluation Q G (Q.shift (r+s) x) (Q.shift (r+s) y)
        (Q.unrolledSheetShiftLinearEquiv k (r+s) x y f) = 0 := by
  rw [Q.unrolledSheetShiftLinearEquiv_add k]
  exact A.arrowPathLinearEvaluation_transport_eq_zero_iff Q G _ _ _

theorem arrowPathLinearEvaluation_shift_step_eq_zero_iff (r : ℤ)
    {x y : Q.LiftVertex} (f : Q.UnrolledPathComponent k x y) :
    A.arrowPathLinearEvaluation Q G (Q.shift (r+1) x) (Q.shift (r+1) y)
      (Q.unrolledSheetShiftLinearEquiv k (r+1) x y f) = 0 ↔
      A.arrowPathLinearEvaluation Q G (Q.shift r x) (Q.shift r y)
        (Q.unrolledSheetShiftLinearEquiv k r x y f) = 0 :=
  (A.arrowPathLinearEvaluation_shift_add_eq_zero_iff Q G r 1 f).symm.trans
    (A.arrowPathLinearEvaluation_shift_eq_zero_iff Q G E hG
      (Q.unrolledSheetShiftLinearEquiv k r x y f))

theorem arrowPathLinearEvaluation_integer_shift_eq_zero_iff (r : ℤ)
    {x y : Q.LiftVertex} (f : Q.UnrolledPathComponent k x y) :
    A.arrowPathLinearEvaluation Q G (Q.shift r x) (Q.shift r y)
      (Q.unrolledSheetShiftLinearEquiv k r x y f) = 0 ↔
      A.arrowPathLinearEvaluation Q G x y f = 0 := by
  induction r using Int.induction_on with
  | zero =>
    rw [Q.unrolledSheetShiftLinearEquiv_zero k]
    exact A.arrowPathLinearEvaluation_transport_eq_zero_iff Q G _ _ _
  | succ n ih =>
    exact (A.arrowPathLinearEvaluation_shift_step_eq_zero_iff Q G E hG n f).trans ih
  | pred n ih =>
    let P : ℤ → Prop := fun s =>
      A.arrowPathLinearEvaluation Q G (Q.shift s x) (Q.shift s y)
        (Q.unrolledSheetShiftLinearEquiv k s x y f) = 0
    have step : P ((-(n : ℤ)-1)+1) ↔ P (-(n : ℤ)-1) :=
      A.arrowPathLinearEvaluation_shift_step_eq_zero_iff Q G E hG (-(n : ℤ)-1) f
    rw [sub_add_cancel] at step
    exact step.symm.trans ih

theorem arrowPathLinearEvaluation_integer_shift_kernel (r : ℤ) (x y : Q.LiftVertex) :
    Submodule.map (Q.unrolledSheetShiftLinearEquiv k r x y).toLinearMap
      (LinearMap.ker (A.arrowPathLinearEvaluation Q G x y)) =
      LinearMap.ker
        (A.arrowPathLinearEvaluation Q G (Q.shift r x) (Q.shift r y)) := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (A.arrowPathLinearEvaluation_integer_shift_eq_zero_iff Q G E hG r g).mpr hg
  · intro hf
    obtain ⟨g, rfl⟩ := (Q.unrolledSheetShiftLinearEquiv k r x y).surjective f
    exact ⟨g, (A.arrowPathLinearEvaluation_integer_shift_eq_zero_iff Q G E hG r g).mp hf, rfl⟩

end ASGinzburg.ZAlgebra
