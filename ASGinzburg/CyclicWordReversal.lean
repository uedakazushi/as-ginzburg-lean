import ASGinzburg.ClosedPathPotentials

/-! Reversal respects the actual rotation quotient, without changing the
definition of a cyclic word or adding an equivalence assumption. -/
namespace ASGinzburg
universe u v
variable {A : Type u} {k : Type v} [Field k]

def reverseCyclicWord : CyclicWord A → CyclicWord A :=
  Quotient.map List.reverse (fun _ _ h => h.reverse)

@[simp] theorem reverseCyclicWord_wordClass (w : List A) :
    reverseCyclicWord (wordClass w) = wordClass w.reverse := rfl

theorem reverseCyclicWord_involutive :
    Function.Involutive (reverseCyclicWord (A := A)) := by
  intro c
  induction c using Quotient.inductionOn with
  | h w =>
    change reverseCyclicWord (reverseCyclicWord (wordClass w)) = wordClass w
    simp

def reverseCyclicWordEquiv : CyclicWord A ≃ CyclicWord A :=
  { toFun := reverseCyclicWord
    invFun := reverseCyclicWord
    left_inv := reverseCyclicWord_involutive
    right_inv := reverseCyclicWord_involutive }

noncomputable def reverseCyclicPolynomial :
    CyclicPolynomial k A ≃ₗ[k] CyclicPolynomial k A :=
  Finsupp.domLCongr reverseCyclicWordEquiv

theorem reverseCyclicPolynomial_involutive :
    Function.Involutive (reverseCyclicPolynomial (k := k) (A := A)) := by
  have h : (reverseCyclicPolynomial (k := k) (A := A)).symm =
      reverseCyclicPolynomial := by
    rw [reverseCyclicPolynomial, Finsupp.domLCongr_symm]
    rfl
  intro φ
  rw [← h]
  exact LinearEquiv.symm_apply_apply _ φ

@[simp] theorem reverseCyclicPolynomial_traceWord (w : List A) :
    reverseCyclicPolynomial (traceWord (k := k) w) = traceWord w.reverse := by
  simp only [reverseCyclicPolynomial, traceWord, Finsupp.domLCongr_single]
  rfl

end ASGinzburg
