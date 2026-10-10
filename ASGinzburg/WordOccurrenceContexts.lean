import ASGinzburg.WordPolynomialConcatenation

/-! Actual occurrence contexts: at an occurrence in prefix·b·suffix,
the input polynomial is inserted as suffix·input·prefix. -/
namespace ASGinzburg
universe u v
variable {A : Type u} {k : Type v} [Field k]

noncomputable def wordOccurrenceSandwich (pre suffix : List A) :
    WordPolynomial k A →ₗ[k] WordPolynomial k A :=
  Finsupp.lmapDomain k k (fun w => suffix ++ w ++ pre)

@[simp] theorem wordOccurrenceSandwich_single (pre suffix w : List A) (c : k) :
    wordOccurrenceSandwich pre suffix (Finsupp.single w c) =
      Finsupp.single (suffix ++ w ++ pre) c := by
  classical
  simp [wordOccurrenceSandwich, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem wordOccurrenceSandwich_eq_concatenation (pre suffix : List A)
    (h : WordPolynomial k A) :
    wordOccurrenceSandwich pre suffix h =
      wordConcatenation (wordConcatenation (Finsupp.single suffix 1) h)
        (Finsupp.single pre 1) := by
  classical
  induction h using Finsupp.induction_linear with
  | zero => simp
  | add h h' hh hh' => simp only [map_add, LinearMap.add_apply, hh, hh']
  | single w c => simp

variable [DecidableEq A]

noncomputable def wordOccurrenceContextAux (b : A) (pre : List A) :
    List A → WordPolynomial k A →ₗ[k] WordPolynomial k A
  | [] => 0
  | a :: s => (if b = a then wordOccurrenceSandwich pre s else 0) +
      wordOccurrenceContextAux b (pre ++ [a]) s

noncomputable def wordOccurrenceContextWord (b : A) (w : List A) :
    WordPolynomial k A →ₗ[k] WordPolynomial k A :=
  wordOccurrenceContextAux b [] w

noncomputable def wordOccurrenceContext (b : A) :
    WordPolynomial k A →ₗ[k] WordPolynomial k A →ₗ[k] WordPolynomial k A :=
  Finsupp.linearCombination k (wordOccurrenceContextWord b)

@[simp] theorem wordOccurrenceContext_single (b : A) (w : List A) (c : k)
    (h : WordPolynomial k A) :
    wordOccurrenceContext b (Finsupp.single w c) h =
      c • wordOccurrenceContextWord b w h := by
  classical
  simp [wordOccurrenceContext]

theorem wordOccurrenceContextAux_unit (b : A) (pre s : List A) :
    wordOccurrenceContextAux b pre s (Finsupp.single [] (1 : k)) =
      derivativeAux b pre s := by
  induction s generalizing pre with
  | nil => simp [wordOccurrenceContextAux, derivativeAux]
  | cons a s ih =>
    by_cases hba : b = a
    · subst a
      simp [wordOccurrenceContextAux, derivativeAux, ih]
    · simp [wordOccurrenceContextAux, derivativeAux, hba, ih]

theorem wordOccurrenceContextWord_unit (b : A) (w : List A) :
    wordOccurrenceContextWord b w (Finsupp.single [] (1 : k)) =
      derivativeWord b w :=
  wordOccurrenceContextAux_unit b [] w

theorem wordOccurrenceContextAux_prefix (b : A) (pre s : List A)
    (h : WordPolynomial k A) :
    wordOccurrenceContextAux b pre s h =
      wordOccurrenceContextAux b [] s (wordConcatenation h (Finsupp.single pre 1)) := by
  induction s generalizing pre h with
  | nil => simp [wordOccurrenceContextAux]
  | cons a s ih =>
    simp only [wordOccurrenceContextAux, LinearMap.add_apply]
    rw [ih (pre ++ [a]) h, ih ([] ++ [a])
      (wordConcatenation h (Finsupp.single pre 1))]
    have hfirst : wordOccurrenceSandwich pre s h =
        wordOccurrenceSandwich [] s (wordConcatenation h (Finsupp.single pre 1)) := by
      simp only [wordOccurrenceSandwich_eq_concatenation, wordConcatenation_unit_right,
        wordConcatenation_assoc]
    have hrest : wordConcatenation h (Finsupp.single (pre ++ [a]) 1) =
        wordConcatenation (wordConcatenation h (Finsupp.single pre 1))
          (Finsupp.single [a] 1) := by
      rw [wordConcatenation_assoc]
      simp
    by_cases hba : b = a <;> simp [hba, hfirst, hrest]

theorem wordOccurrenceContextWord_cons (b a : A) (s : List A)
    (h : WordPolynomial k A) :
    wordOccurrenceContextWord b (a :: s) h =
      (if b = a then wordConcatenation (Finsupp.single s 1) h else 0) +
        wordOccurrenceContextWord b s (wordConcatenation h (Finsupp.single [a] 1)) := by
  simp only [wordOccurrenceContextWord, wordOccurrenceContextAux, LinearMap.add_apply]
  rw [wordOccurrenceContextAux_prefix]
  by_cases hba : b = a <;>
    simp [hba, wordOccurrenceSandwich_eq_concatenation]

theorem wordOccurrenceContextWord_append (b : A) (p q : List A)
    (h : WordPolynomial k A) :
    wordOccurrenceContextWord b (p ++ q) h =
      wordOccurrenceContextWord b p (wordConcatenation (Finsupp.single q 1) h) +
        wordOccurrenceContextWord b q (wordConcatenation h (Finsupp.single p 1)) := by
  induction p generalizing h with
  | nil => simp [wordOccurrenceContextWord, wordOccurrenceContextAux]
  | cons a p ih =>
    simp only [List.cons_append, wordOccurrenceContextWord_cons, ih]
    have hrest : wordConcatenation (wordConcatenation h (Finsupp.single [a] 1))
        (Finsupp.single p 1) = wordConcatenation h (Finsupp.single (a :: p) 1) := by
      rw [wordConcatenation_assoc]
      simp
    rw [hrest]
    by_cases hba : b = a <;>
      simp [hba, ← wordConcatenation_assoc, add_assoc]

end ASGinzburg
