import ASGinzburg.FoundationPeriodEvaluationCoherence
import ASGinzburg.FoundationPeriodZeroKernel
import ASGinzburg.ArbitraryArrowKernelHeights

/-! All same-sheet kernels of the actual AS periodic presentation
are the native translates of the original foundation evaluation kernels. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem ASRegular.foundationPeriodPathLinearEvaluation_zeroSheet_eq
    (hAS : A.ASRegular Q) (i j : Q.Vertex) :
    A.arrowPathLinearEvaluation Q (hAS.foundationPeriodIncomingElement A Q) (i,0) (j,0) =
      A.unrolledPathLinearEvaluation Q (hAS.resolution A Q) (i,0) (j,0) := by
  apply LinearMap.ext
  exact hAS.foundationPeriodPathLinearEvaluation_zeroSheet_of_sheet A Q _ _ rfl rfl

theorem ASRegular.foundationPeriodPathLinearEvaluation_sheet_kernel
    (hAS : A.ASRegular Q) (m : ℤ) (i j : Q.Vertex) :
    Submodule.map (Q.unrolledSheetShiftLinearEquiv k m (i,0) (j,0)).toLinearMap
        (LinearMap.ker (A.unrolledPathLinearEvaluation Q (hAS.resolution A Q) (i,0) (j,0))) =
      LinearMap.ker (A.arrowPathLinearEvaluation Q
        (hAS.foundationPeriodIncomingElement A Q) (Q.shift m (i,0)) (Q.shift m (j,0))) := by
  rw [← hAS.foundationPeriodPathLinearEvaluation_zeroSheet_eq A Q i j]
  exact hAS.foundationPeriodPathLinearEvaluation_integer_shift_kernel A Q m (i,0) (j,0)

end ASGinzburg.ZAlgebra
