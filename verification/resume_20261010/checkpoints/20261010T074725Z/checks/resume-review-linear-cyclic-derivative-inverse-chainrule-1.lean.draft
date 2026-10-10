import work.ASGinzburgDraft.LinearCyclicDerivativeChainRule

/-! A proved inverse arrow matrix turns the actual cyclic chain rule
into the precise contragredient formula for dual generator differentials. -/
namespace ASGinzburg
universe u v
variable {A : Type u} [DecidableEq A] [Fintype A] {k : Type v} [Field k]

theorem linear_cyclicDerivative_inverse_chainRule
    (C D : A → A → k)
    (hCD : ∀ a b : A, (∑ i : A, C a i * D i b) = if a = b then 1 else 0)
    (b : A) (φ : CyclicPolynomial k A) :
    wordSubstitution (wordLinearArrowReplacement C) (cyclicDerivative b φ) =
      ∑ i : A, D i b • cyclicDerivative i
        (cyclicSubstitution (wordLinearArrowReplacement C) φ) := by
  classical
  symm
  simp only [linear_cyclicDerivative_chainRule,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  simp_rw [←Finset.sum_smul]
  have hsum : ∀ a : A, (∑ i : A, D i b * C a i) = if a = b then 1 else 0 := by
    intro a
    simpa only [mul_comm] using hCD a b
  simp_rw [hsum]
  simp

end ASGinzburg
