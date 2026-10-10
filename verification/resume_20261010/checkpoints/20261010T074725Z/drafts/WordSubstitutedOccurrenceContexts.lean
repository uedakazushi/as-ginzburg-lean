import work.ASGinzburgDraft.WordSubstitutedOccurrenceContextsSubstitution
import ASGinzburg.WordOccurrenceContexts

/-! Genuine mixed-alphabet occurrence insertion. At every occurrence of a
letter, substituted suffix and prefix surround an arbitrary input polynomial. -/
namespace ASGinzburg
universe u v z
variable {A : Type u} {B : Type v} {k : Type z} [Field k]

noncomputable def wordSubstitutedOccurrenceSandwich
    (σ : A → WordPolynomial k B) (pre suffix : List A) :
    WordPolynomial k B →ₗ[k] WordPolynomial k B :=
  (wordConcatenation.flip (wordSubstitutionBetweenWord σ pre)).comp
    (wordConcatenation (wordSubstitutionBetweenWord σ suffix))

theorem wordSubstitutedOccurrenceSandwich_apply
    (σ : A → WordPolynomial k B) (pre suffix : List A) (h : WordPolynomial k B) :
    wordSubstitutedOccurrenceSandwich σ pre suffix h =
      wordConcatenation (wordConcatenation (wordSubstitutionBetweenWord σ suffix) h)
        (wordSubstitutionBetweenWord σ pre) := rfl

variable [DecidableEq A]

noncomputable def wordSubstitutedOccurrenceContextAux
    (σ : A → WordPolynomial k B) (a : A) (pre : List A) :
    List A → WordPolynomial k B →ₗ[k] WordPolynomial k B
  | [] => 0
  | c :: s => (if a = c then wordSubstitutedOccurrenceSandwich σ pre s else 0) +
      wordSubstitutedOccurrenceContextAux σ a (pre ++ [c]) s

noncomputable def wordSubstitutedOccurrenceContextWord
    (σ : A → WordPolynomial k B) (a : A) (w : List A) :
    WordPolynomial k B →ₗ[k] WordPolynomial k B :=
  wordSubstitutedOccurrenceContextAux σ a [] w

noncomputable def wordSubstitutedOccurrenceContext
    (σ : A → WordPolynomial k B) (a : A) :
    WordPolynomial k A →ₗ[k] WordPolynomial k B →ₗ[k] WordPolynomial k B :=
  Finsupp.linearCombination k (wordSubstitutedOccurrenceContextWord σ a)

@[simp] theorem wordSubstitutedOccurrenceContext_single
    (σ : A → WordPolynomial k B) (a : A) (w : List A) (c : k)
    (h : WordPolynomial k B) :
    wordSubstitutedOccurrenceContext σ a (Finsupp.single w c) h =
      c • wordSubstitutedOccurrenceContextWord σ a w h := by
  classical
  simp [wordSubstitutedOccurrenceContext]

theorem wordSubstitutedOccurrenceContextAux_prefix
    (σ : A → WordPolynomial k B) (a : A) (pre s : List A)
    (h : WordPolynomial k B) :
    wordSubstitutedOccurrenceContextAux σ a pre s h =
      wordSubstitutedOccurrenceContextAux σ a [] s
        (wordConcatenation h (wordSubstitutionBetweenWord σ pre)) := by
  induction s generalizing pre h with
  | nil => simp [wordSubstitutedOccurrenceContextAux]
  | cons c s ih =>
    simp only [wordSubstitutedOccurrenceContextAux, LinearMap.add_apply]
    rw [ih (pre ++ [c]) h, ih ([] ++ [c])
      (wordConcatenation h (wordSubstitutionBetweenWord σ pre))]
    have hfirst : wordSubstitutedOccurrenceSandwich σ pre s h =
        wordSubstitutedOccurrenceSandwich σ [] s
          (wordConcatenation h (wordSubstitutionBetweenWord σ pre)) := by
      simp only [wordSubstitutedOccurrenceSandwich_apply, wordSubstitutionBetweenWord,
        wordConcatenation_unit_right, wordConcatenation_assoc]
    have hrest : wordConcatenation h (wordSubstitutionBetweenWord σ (pre ++ [c])) =
        wordConcatenation (wordConcatenation h (wordSubstitutionBetweenWord σ pre)) (σ c) := by
      rw [wordSubstitutionBetweenWord_append, wordConcatenation_assoc]
      simp only [wordSubstitutionBetweenWord, wordConcatenation_unit_right]
    by_cases hac : a = c <;>
      simp only [hac, if_true, if_false, LinearMap.zero_apply, hfirst, hrest,
        wordSubstitutionBetweenWord, List.nil_append, wordConcatenation_unit_right]

theorem wordSubstitutedOccurrenceContextWord_cons
    (σ : A → WordPolynomial k B) (a c : A) (s : List A)
    (h : WordPolynomial k B) :
    wordSubstitutedOccurrenceContextWord σ a (c :: s) h =
      (if a = c then wordConcatenation (wordSubstitutionBetweenWord σ s) h else 0) +
        wordSubstitutedOccurrenceContextWord σ a s (wordConcatenation h (σ c)) := by
  simp only [wordSubstitutedOccurrenceContextWord, wordSubstitutedOccurrenceContextAux,
    LinearMap.add_apply]
  rw [wordSubstitutedOccurrenceContextAux_prefix]
  by_cases hac : a = c <;>
    simp [hac, wordSubstitutedOccurrenceSandwich_apply, wordSubstitutionBetweenWord]

theorem wordSubstitutedOccurrenceContextWord_append
    (σ : A → WordPolynomial k B) (a : A) (p q : List A)
    (h : WordPolynomial k B) :
    wordSubstitutedOccurrenceContextWord σ a (p ++ q) h =
      wordSubstitutedOccurrenceContextWord σ a p
        (wordConcatenation (wordSubstitutionBetweenWord σ q) h) +
      wordSubstitutedOccurrenceContextWord σ a q
        (wordConcatenation h (wordSubstitutionBetweenWord σ p)) := by
  induction p generalizing h with
  | nil => simp [wordSubstitutedOccurrenceContextWord, wordSubstitutedOccurrenceContextAux,
      wordSubstitutionBetweenWord]
  | cons c p ih =>
    simp only [List.cons_append, wordSubstitutedOccurrenceContextWord_cons, ih,
      wordSubstitutionBetweenWord_append]
    have hrest : wordConcatenation (wordConcatenation h (σ c))
        (wordSubstitutionBetweenWord σ p) =
        wordConcatenation h (wordSubstitutionBetweenWord σ (c :: p)) := by
      rw [wordSubstitutionBetweenWord, wordConcatenation_assoc]
    rw [hrest]
    by_cases hac : a = c <;>
      simp [hac, wordSubstitutionBetweenWord, ← wordConcatenation_assoc, add_assoc]

theorem wordSubstitutedOccurrenceContext_concatenation
    (σ : A → WordPolynomial k B) (a : A)
    (f g : WordPolynomial k A) (h : WordPolynomial k B) :
    wordSubstitutedOccurrenceContext σ a (wordConcatenation f g) h =
      wordSubstitutedOccurrenceContext σ a f (wordConcatenation (wordSubstitutionBetween σ g) h) +
      wordSubstitutedOccurrenceContext σ a g (wordConcatenation h (wordSubstitutionBetween σ f)) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f f' hf hf' =>
    simp only [map_add, LinearMap.add_apply, hf, hf']
    abel
  | single p c =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g g' hg hg' =>
      simp only [map_add, LinearMap.add_apply, hg, hg']
      abel
    | single q d =>
      simp only [wordConcatenation_single, wordSubstitutedOccurrenceContext_single,
        wordSubstitutionBetween_single, wordSubstitutedOccurrenceContextWord_append,
        map_smul, LinearMap.smul_apply, smul_smul, smul_add]
      rw [mul_comm d c]

end ASGinzburg
