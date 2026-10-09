import ASGinzburg.UnrolledLinearShiftArithmetic
import ASGinzburg.UnrolledJacobianLiftIdeal

/-! Forgetting the sheets of a finite path sum commutes with every
native sheet shift; all erasure relations are therefore preserved. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem unrolledSheetShiftLinearEquiv_erase (r : ℤ) {x y : Q.LiftVertex}
    (f : Q.UnrolledPathComponent k x y) :
    Q.unrolledPathEraseLinearMap k (Q.shift r x) (Q.shift r y)
      (Q.unrolledSheetShiftLinearEquiv k r x y f) =
      Q.unrolledPathEraseLinearMap k x y f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [map_add, hf, hg]
  | single p c =>
    simp only [unrolledSheetShiftLinearEquiv_single, unrolledPathEraseLinearMap_single,
      UnrolledPath.erase_shift]

theorem unrolledSheetShiftLinearEquiv_mem_erasureIdeal (I : Q.PathLinearIdeal k)
    (r : ℤ) {x y : Q.LiftVertex} (f : Q.UnrolledPathComponent k x y) :
    Q.unrolledPathEraseLinearMap k (Q.shift r x) (Q.shift r y)
      (Q.unrolledSheetShiftLinearEquiv k r x y f) ∈ I.hom x.1 y.1 ↔
      Q.unrolledPathEraseLinearMap k x y f ∈ I.hom x.1 y.1 := by
  rw [Q.unrolledSheetShiftLinearEquiv_erase k]

end ASGinzburg.CutQuiver
