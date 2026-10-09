import ASGinzburg.CyclicHessianWords
import ASGinzburg.CyclicDerivativeReversal

/-! Reversal of the actual potential transposes and reverses its actual
cyclic Hessian entries. -/
namespace ASGinzburg
universe u v
variable {A : Type u} [DecidableEq A] {k : Type v} [Field k]

omit [DecidableEq A] in
@[simp] theorem reverseWordPolynomial_apply (f : WordPolynomial k A) (w : List A) :
    reverseWordPolynomial f w = f w.reverse := rfl

variable [Fintype A]

theorem cyclicHessianWord_reverse (a b : A) (φ : CyclicPolynomial k A) :
    cyclicHessianWord b a (reverseCyclicPolynomial φ) =
      reverseWordPolynomial (cyclicHessianWord a b φ) := by
  ext w
  rw [cyclicHessianWord_apply,←cyclicDerivative_reverse,reverseWordPolynomial_apply,
    List.reverse_append,List.reverse_singleton,List.singleton_append,
    reverseWordPolynomial_apply,cyclicHessianWord_apply]
  exact (cyclicDerivative_mixed_coeff φ a b w.reverse).symm

end ASGinzburg
