import ASGinzburg.FoundationPeriodEvaluationCoherence
import ASGinzburg.FoundationPeriodZeroKernel
import ASGinzburg.UnrolledSheetShiftErasure
import ASGinzburg.ASFoundationDerivativeUnrolling

/-! The actual cut derivatives of the original AS foundation potential,
lifted to every integer sheet by the native path shift, vanish in the
concrete periodic presentation. No statement is made about the other derivatives. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem ASRegular.foundationCutDerivativeUnroll_period_eval_zero (hAS : A.ASRegular Q)
    (r : ℤ) (b : {a : Q.Arrow // Q.cut a=true}) :
    A.arrowPathLinearEvaluation Q (hAS.foundationPeriodIncomingElement A Q)
      (Q.shift r (Q.target b.val,0)) (Q.shift r (Q.source b.val,0))
      (Q.unrolledSheetShiftLinearEquiv k r (Q.target b.val,0) (Q.source b.val,0)
        (hAS.foundationCutDerivativeUnroll A Q b)) = 0 := by
  apply (hAS.foundationPeriodPathLinearEvaluation_integer_shift_eq_zero_iff A Q r _).mpr
  rw [hAS.foundationPeriodPathLinearEvaluation_zeroSheet_of_sheet A Q _ _ rfl rfl]
  exact hAS.foundationCutDerivativeUnroll_eval_zero A Q b

theorem ASRegular.foundationCutDerivativeUnroll_period_erase (hAS : A.ASRegular Q)
    (r : ℤ) (b : {a : Q.Arrow // Q.cut a=true}) :
    Q.unrolledPathEraseLinearMap k
      (Q.shift r (Q.target b.val,0)) (Q.shift r (Q.source b.val,0))
      (Q.unrolledSheetShiftLinearEquiv k r (Q.target b.val,0) (Q.source b.val,0)
        (hAS.foundationCutDerivativeUnroll A Q b)) =
      Q.pathCyclicDerivative k b.val (hAS.foundationPotential A Q) := by
  rw [Q.unrolledSheetShiftLinearEquiv_erase k]
  exact Q.pathCutUnrollingEquiv_erase k (Q.target b.val) (Q.source b.val) 0 0
    ⟨Q.pathCyclicDerivative k b.val (hAS.foundationPotential A Q),by
      rw [hAS.foundationPotential_pathCyclicDerivative A Q b]
      exact hAS.cutPathRelation_cut A Q b⟩

end ASGinzburg.ZAlgebra
