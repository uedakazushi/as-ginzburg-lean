import ASGinzburg.NonlinearCyclicDerivativeChainRule

/-! The true cyclic derivative chain rule for finite linear arrow
substitutions, derived from singleton occurrence contexts. -/
namespace ASGinzburg
universe u v
variable {A : Type u} [DecidableEq A] [Fintype A] {k : Type v} [Field k]

noncomputable def wordLinearArrowReplacement (C : A → A → k) :
    A → WordPolynomial k A :=
  fun a => ∑ b : A, Finsupp.single [b] (C a b)

omit [Fintype A] in
theorem wordOccurrenceContext_singleton (b a : A) (c : k)
    (h : WordPolynomial k A) :
    wordOccurrenceContext b (Finsupp.single [a] c) h =
      if b = a then c • h else 0 := by
  rw [wordOccurrenceContext_single,wordOccurrenceContextWord_cons]
  by_cases hba : b = a <;>
    simp [hba,wordOccurrenceContextWord,wordOccurrenceContextAux]

theorem wordOccurrenceContext_linearArrowReplacement
    (C : A → A → k) (b a : A) (h : WordPolynomial k A) :
    wordOccurrenceContext b (wordLinearArrowReplacement C a) h = C a b • h := by
  classical
  simp only [wordLinearArrowReplacement,map_sum,LinearMap.sum_apply,
    wordOccurrenceContext_singleton]
  simp

theorem linear_cyclicDerivative_chainRule (C : A → A → k)
    (b : A) (φ : CyclicPolynomial k A) :
    cyclicDerivative b (cyclicSubstitution (wordLinearArrowReplacement C) φ) =
      ∑ a : A, C a b • wordSubstitution (wordLinearArrowReplacement C)
        (cyclicDerivative a φ) := by
  rw [nonlinear_cyclicDerivative_chainRule]
  simp only [wordOccurrenceContext_linearArrowReplacement]

end ASGinzburg
