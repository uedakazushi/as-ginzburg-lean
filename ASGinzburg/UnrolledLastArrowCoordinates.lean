import ASGinzburg.UnrolledPathFiniteness
import ASGinzburg.UnrolledPathAlgebra
import Mathlib.LinearAlgebra.Finsupp.SumProd

/-! Off the diagonal, every actual unrolled path has a unique last
incoming arrow. Its genuine linear coordinates are the corresponding
prefix path components, needed for the minimal-relation kernel bridge. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

def unrolledLastArrowEquiv (u v : Q.LiftVertex) (huv : u≠v) :
    Q.UnrolledPath u v ≃
      (Σ a : Q.incomingArrows v, Q.UnrolledPath u (Q.incomingSource v a)) where
  toFun p := match p with
    | .nil _ => False.elim (huv rfl)
    | .snoc a p => ⟨a,p⟩
  invFun p := .snoc p.1 p.2
  left_inv p := by
    cases p with
    | nil => exact False.elim (huv rfl)
    | snoc a p => rfl
  right_inv p := by cases p; rfl

noncomputable def unrolledLastArrowLinearEquiv (u v : Q.LiftVertex) (huv : u≠v) :
    Q.UnrolledPathComponent k u v ≃ₗ[k]
      (∀ a : Q.incomingArrows v, Q.UnrolledPathComponent k u (Q.incomingSource v a)) :=
  (Finsupp.domLCongr (Q.unrolledLastArrowEquiv u v huv)).trans
    (Finsupp.sigmaFinsuppLEquivPiFinsupp k)

theorem unrolledLastArrowLinearEquiv_apply (u v : Q.LiftVertex) (huv : u≠v)
    (f : Q.UnrolledPathComponent k u v) (a : Q.incomingArrows v)
    (p : Q.UnrolledPath u (Q.incomingSource v a)) :
    Q.unrolledLastArrowLinearEquiv k u v huv f a p=f (.snoc a p) := by
  simp [unrolledLastArrowLinearEquiv,Finsupp.domLCongr_apply,unrolledLastArrowEquiv]

end ASGinzburg.CutQuiver
