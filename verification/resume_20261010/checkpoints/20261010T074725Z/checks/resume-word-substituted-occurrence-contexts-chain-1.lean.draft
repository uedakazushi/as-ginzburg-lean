import work.ASGinzburgDraft.WordSubstitutedOccurrenceContexts
import ASGinzburg.WordOccurrenceProductRule

/-! The occurrence chain rule inserts an arbitrary polynomial, rather than
assuming any cyclic derivative identity. All sums are the actual occurrence sums. -/
namespace ASGinzburg
universe u v z
variable {A : Type u} {B : Type v} {k : Type z} [Field k]
variable [DecidableEq A] [DecidableEq B] [Fintype A]

theorem wordSubstitutedOccurrenceContextWord_chain
    (σ : A → WordPolynomial k B) (b : B) (w : List A) (h : WordPolynomial k B) :
    wordOccurrenceContext b (wordSubstitutionBetweenWord σ w) h =
      ∑ a : A, wordOccurrenceContext b (σ a)
        (wordSubstitutedOccurrenceContextWord σ a w h) := by
  classical
  induction w generalizing h with
  | nil => simp [wordSubstitutionBetweenWord, wordOccurrenceContextWord,
      wordOccurrenceContextAux, wordSubstitutedOccurrenceContextWord,
      wordSubstitutedOccurrenceContextAux]
  | cons c w ih =>
    rw [wordSubstitutionBetweenWord, wordOccurrenceContext_concatenation, ih]
    simp_rw [wordSubstitutedOccurrenceContextWord_cons]
    simp only [map_add, Finset.sum_add_distrib]
    have hfirst (a : A) :
        wordOccurrenceContext b (σ a)
          (if a = c then wordConcatenation (wordSubstitutionBetweenWord σ w) h else 0) =
        if a = c then wordOccurrenceContext b (σ c)
          (wordConcatenation (wordSubstitutionBetweenWord σ w) h) else 0 := by
      by_cases hac : a = c
      · subst a
        rw [if_pos rfl, if_pos rfl]
      · rw [if_neg hac, if_neg hac, map_zero]
    simp_rw [hfirst]
    simp

theorem wordSubstitutedOccurrenceContext_chain
    (σ : A → WordPolynomial k B) (b : B) (f : WordPolynomial k A)
    (h : WordPolynomial k B) :
    wordOccurrenceContext b (wordSubstitutionBetween σ f) h =
      ∑ a : A, wordOccurrenceContext b (σ a)
        (wordSubstitutedOccurrenceContext σ a f h) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, LinearMap.add_apply, hf, hg,
      Finset.sum_add_distrib]
  | single w c =>
    simp only [wordSubstitutionBetween_single, map_smul, LinearMap.smul_apply,
      wordSubstitutedOccurrenceContext_single, ← Finset.smul_sum]
    rw [wordSubstitutedOccurrenceContextWord_chain]

end ASGinzburg
