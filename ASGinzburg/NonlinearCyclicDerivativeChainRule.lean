import ASGinzburg.WordOccurrenceProductRule
import ASGinzburg.WordPolynomialSubstitution

/-! The cyclic chain rule for arbitrary finite noncommutative substitutions.
Every term is the actual sum over occurrences in an arrow image. -/
namespace ASGinzburg
universe u v
variable {A : Type u} [DecidableEq A] {k : Type v} [Field k]

noncomputable def wordSubstitutionChainAux (σ : A → WordPolynomial k A)
    (b : A) (pre : WordPolynomial k A) : List A → WordPolynomial k A → WordPolynomial k A
  | [], _ => 0
  | a :: s, h =>
      wordOccurrenceContext b (σ a)
        (wordConcatenation (wordConcatenation (wordSubstitutionWord σ s) h) pre) +
        wordSubstitutionChainAux σ b (wordConcatenation pre (σ a)) s h

theorem wordOccurrenceContext_substitutionChain (σ : A → WordPolynomial k A)
    (b : A) (pre : WordPolynomial k A) (s : List A) (h : WordPolynomial k A) :
    wordOccurrenceContext b (wordSubstitutionWord σ s) (wordConcatenation h pre) =
      wordSubstitutionChainAux σ b pre s h := by
  induction s generalizing pre h with
  | nil => simp [wordSubstitutionWord, wordOccurrenceContextWord,
      wordOccurrenceContextAux, wordSubstitutionChainAux]
  | cons a s ih =>
    simp only [wordSubstitutionWord, wordOccurrenceContext_concatenation,
      wordSubstitutionChainAux, wordConcatenation_assoc, ih]

variable [Fintype A]

theorem wordSubstitutionChainAux_derivativeAux (σ : A → WordPolynomial k A)
    (b : A) (pre s : List A) :
    wordSubstitutionChainAux σ b (wordSubstitutionWord σ pre) s (Finsupp.single [] 1) =
      ∑ a, wordOccurrenceContext b (σ a) (wordSubstitution σ (derivativeAux a pre s)) := by
  classical
  induction s generalizing pre with
  | nil => simp [wordSubstitutionChainAux, derivativeAux]
  | cons a s ih =>
    have hpre : wordSubstitutionWord σ (pre ++ [a]) =
        wordConcatenation (wordSubstitutionWord σ pre) (σ a) := by
      simp [wordSubstitutionWord_append, wordSubstitutionWord]
    rw [wordSubstitutionChainAux, wordConcatenation_unit_right, ← hpre, ih]
    have hterm (c : A) :
        wordOccurrenceContext b (σ c)
            (wordSubstitution σ (derivativeAux c pre (a :: s))) =
          (if c = a then wordOccurrenceContext b (σ a)
            (wordConcatenation (wordSubstitutionWord σ s) (wordSubstitutionWord σ pre))
          else 0) +
            wordOccurrenceContext b (σ c)
              (wordSubstitution σ (derivativeAux c (pre ++ [a]) s)) := by
      by_cases hca : c = a
      · subst c
        simp [derivativeAux, wordSubstitutionWord_append]
      · simp [derivativeAux, hca]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib]
    simp

theorem cyclicDerivative_substitution_traceWord (σ : A → WordPolynomial k A)
    (b : A) (w : List A) :
    cyclicDerivative b (cyclicSubstitution σ (traceWord w)) =
      ∑ a, wordOccurrenceContext b (σ a) (wordSubstitution σ (derivativeWord a w)) := by
  rw [cyclicSubstitution_traceWord, ← wordOccurrenceContext_unit]
  have h := wordOccurrenceContext_substitutionChain σ b (Finsupp.single [] 1) w
    (Finsupp.single [] 1)
  simp only [wordConcatenation_unit_right] at h
  rw [h]
  simpa only [wordSubstitutionWord, derivativeWord] using
    wordSubstitutionChainAux_derivativeAux σ b [] w

theorem nonlinear_cyclicDerivative_chainRule (σ : A → WordPolynomial k A)
    (b : A) (φ : CyclicPolynomial k A) :
    cyclicDerivative b (cyclicSubstitution σ φ) =
      ∑ a, wordOccurrenceContext b (σ a) (wordSubstitution σ (cyclicDerivative a φ)) := by
  classical
  induction φ using Finsupp.induction_linear with
  | zero => simp
  | add φ ψ hφ hψ => simp only [map_add, Finset.sum_add_distrib, hφ, hψ]
  | single c x =>
    obtain ⟨w, rfl⟩ := Quotient.exists_rep c
    have hs : Finsupp.single (wordClass w) x = x • traceWord (k := k) w := by
      simp [traceWord]
    change cyclicDerivative b (cyclicSubstitution σ (Finsupp.single (wordClass w) x)) =
      ∑ a, wordOccurrenceContext b (σ a)
        (wordSubstitution σ (cyclicDerivative a (Finsupp.single (wordClass w) x)))
    rw [hs]
    simp only [map_smul, cyclicDerivative_traceWord, ← Finset.smul_sum]
    rw [cyclicDerivative_substitution_traceWord]

end ASGinzburg
