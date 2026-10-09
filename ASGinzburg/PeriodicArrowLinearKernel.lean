import ASGinzburg.PeriodicArrowPathEvaluation

/-! The periodic evaluation comparison extends to every finite linear
combination and identifies the actual kernels on adjacent sheets. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)
variable (G : A.IncomingElementFamily Q) (E : A.PeriodIso Q.vertices)
variable (hG : G.PeriodCoherent A Q E)
include E hG

theorem arrowPathLinearEvaluation_shift {x y : Q.LiftVertex}
    (f : Q.UnrolledPathComponent k x y) :
    A.arrowPathLinearEvaluation Q G (Q.shift 1 x) (Q.shift 1 y)
      (Q.unrolledSheetShiftLinearEquiv k 1 x y f) =
      E.liftedStepMap A Q x y (A.arrowPathLinearEvaluation Q G x y f) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [map_add, hf, hg]
  | single p c =>
    simp only [CutQuiver.unrolledSheetShiftLinearEquiv_single,
      arrowPathLinearEvaluation_single, map_smul,
      A.arrowPathEvaluation_shift Q G E hG p]

theorem arrowPathLinearEvaluation_shift_eq_zero_iff {x y : Q.LiftVertex}
    (f : Q.UnrolledPathComponent k x y) :
    A.arrowPathLinearEvaluation Q G (Q.shift 1 x) (Q.shift 1 y)
      (Q.unrolledSheetShiftLinearEquiv k 1 x y f) = 0 ↔
      A.arrowPathLinearEvaluation Q G x y f = 0 := by
  rw [A.arrowPathLinearEvaluation_shift Q G E hG]
  exact (E.liftedStepMap A Q x y).map_eq_zero_iff

theorem arrowPathLinearEvaluation_shift_kernel (x y : Q.LiftVertex) :
    Submodule.map (Q.unrolledSheetShiftLinearEquiv k 1 x y).toLinearMap
      (LinearMap.ker (A.arrowPathLinearEvaluation Q G x y)) =
      LinearMap.ker
        (A.arrowPathLinearEvaluation Q G (Q.shift 1 x) (Q.shift 1 y)) := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (A.arrowPathLinearEvaluation_shift_eq_zero_iff Q G E hG g).mpr hg
  · intro hf
    obtain ⟨g, rfl⟩ := (Q.unrolledSheetShiftLinearEquiv k 1 x y).surjective f
    exact ⟨g, (A.arrowPathLinearEvaluation_shift_eq_zero_iff Q G E hG g).mp hf, rfl⟩

end ASGinzburg.ZAlgebra
