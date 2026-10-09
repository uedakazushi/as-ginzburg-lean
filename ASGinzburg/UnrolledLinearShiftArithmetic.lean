import ASGinzburg.UnrolledPathShiftArithmetic
import ASGinzburg.UnrolledComponentHeights

/-! The actual finite-linear sheet maps obey the zero and addition
laws, with every endpoint change represented by its native path map. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem unrolledSheetShiftLinearEquiv_zero {x y : Q.LiftVertex}
    (f : Q.UnrolledPathComponent k x y) :
    Q.unrolledSheetShiftLinearEquiv k 0 x y f =
      Finsupp.mapDomain (UnrolledPath.endpointEquiv Q
        (by simp [CutQuiver.shift]) (by simp [CutQuiver.shift])) f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [map_add, Finsupp.mapDomain_add, hf, hg]
  | single p c =>
    rw [unrolledSheetShiftLinearEquiv_single, Finsupp.mapDomain_single]
    exact congrArg (fun q => Finsupp.single q c) p.shift_zero

theorem unrolledSheetShiftLinearEquiv_add (r s : ℤ) {x y : Q.LiftVertex}
    (f : Q.UnrolledPathComponent k x y) :
    Q.unrolledSheetShiftLinearEquiv k s (Q.shift r x) (Q.shift r y)
      (Q.unrolledSheetShiftLinearEquiv k r x y f) =
      Finsupp.mapDomain (UnrolledPath.endpointEquiv Q
        (by simp [CutQuiver.shift, add_assoc])
        (by simp [CutQuiver.shift, add_assoc]))
        (Q.unrolledSheetShiftLinearEquiv k (r+s) x y f) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [map_add, Finsupp.mapDomain_add, hf, hg]
  | single p c =>
    rw [unrolledSheetShiftLinearEquiv_single, unrolledSheetShiftLinearEquiv_single,
      unrolledSheetShiftLinearEquiv_single, Finsupp.mapDomain_single]
    exact congrArg (fun q => Finsupp.single q c) (p.shift_add r s)

end ASGinzburg.CutQuiver
