import work.ASGinzburgDraft.WordOccurrenceContexts

/-! The genuine noncommutative product rule for cyclic occurrence contexts. -/
namespace ASGinzburg
universe u v
variable {A : Type u} [DecidableEq A] {k : Type v} [Field k]

theorem wordOccurrenceContext_concatenation (b : A) (f g h : WordPolynomial k A) :
    wordOccurrenceContext b (wordConcatenation f g) h =
      wordOccurrenceContext b f (wordConcatenation g h) +
        wordOccurrenceContext b g (wordConcatenation h f) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f f' hf hf' =>
    simp only [map_add, LinearMap.add_apply, hf, hf']
    abel
  | single p a =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g g' hg hg' =>
      simp only [map_add, LinearMap.add_apply, hg, hg']
      abel
    | single q c =>
      have hp : Finsupp.single p a = a • Finsupp.single p (1 : k) := by simp
      have hq : Finsupp.single q c = c • Finsupp.single q (1 : k) := by simp
      rw [hp, hq]
      simp only [map_smul, LinearMap.smul_apply, smul_smul, wordConcatenation_single,
        one_mul, wordOccurrenceContext_single, one_smul,
        wordOccurrenceContextWord_append, smul_add]
      rw [mul_comm c a]

theorem wordOccurrenceContext_unit (b : A) (f : WordPolynomial k A) :
    wordOccurrenceContext b f (Finsupp.single [] 1) =
      cyclicDerivative b (cyclicTrace f) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, LinearMap.add_apply, hf, hg]
  | single p a =>
    simp [wordOccurrenceContextWord_unit, cyclicTrace, cyclicDerivative,
      traceWord, derivativeCyclicWord_mk]

end ASGinzburg
