import ASGinzburg.CyclicDerivativeMixedCoefficients

/-! Actual first/last arrow coefficient operators and cyclic Hessian
entries are linear maps on finite word polynomials. Their equality is
proved from the actual cyclic derivative, not added as a hypothesis. -/
namespace ASGinzburg
universe u v
variable {A : Type u} [DecidableEq A] {k : Type v} [Field k]

noncomputable def stripFirstWord (a : A) : WordPolynomial k A →ₗ[k] WordPolynomial k A :=
  Finsupp.lcomapDomain (R := k) (M := k) (List.cons a) (by
    intro x y h
    exact (List.cons.inj h).2)

noncomputable def stripLastWord (b : A) : WordPolynomial k A →ₗ[k] WordPolynomial k A :=
  Finsupp.lcomapDomain (R := k) (M := k) (fun w => w++[b]) (by
    intro x y h
    exact List.append_cancel_right h)

omit [DecidableEq A] in
@[simp] theorem stripFirstWord_apply (a : A) (f : WordPolynomial k A) (w : List A) :
    stripFirstWord a f w = f (a::w) := rfl

omit [DecidableEq A] in
@[simp] theorem stripLastWord_apply (b : A) (f : WordPolynomial k A) (w : List A) :
    stripLastWord b f w = f (w++[b]) := rfl

noncomputable def cyclicHessianWord (a b : A) :
    CyclicPolynomial k A →ₗ[k] WordPolynomial k A :=
  (stripLastWord b).comp (cyclicDerivative a)

@[simp] theorem cyclicHessianWord_apply (a b : A) (φ : CyclicPolynomial k A) (w : List A) :
    cyclicHessianWord a b φ w = cyclicDerivative a φ (w++[b]) := rfl

variable [Fintype A]

theorem cyclicHessianWord_eq_stripFirst (a b : A) (φ : CyclicPolynomial k A) :
    cyclicHessianWord a b φ = stripFirstWord a (cyclicDerivative b φ) := by
  ext w
  exact cyclicDerivative_mixed_coeff φ a b w

theorem cyclicHessianWord_linearMap_eq (a b : A) :
    cyclicHessianWord (k := k) a b = (stripFirstWord a).comp (cyclicDerivative b) := by
  apply LinearMap.ext
  intro φ
  exact cyclicHessianWord_eq_stripFirst a b φ

end ASGinzburg
