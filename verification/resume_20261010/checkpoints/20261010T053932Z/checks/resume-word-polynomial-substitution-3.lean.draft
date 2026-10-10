import work.ASGinzburgDraft.WordPolynomialConcatenation

/-! Arbitrary finite word-polynomial substitutions act on the actual
rotation quotient. No linearity or homogeneity of the arrow images is assumed. -/
namespace ASGinzburg
universe u v
variable {A : Type u} {k : Type v} [Field k]

noncomputable def wordSubstitutionWord (σ : A → WordPolynomial k A) :
    List A → WordPolynomial k A
  | [] => Finsupp.single [] 1
  | a :: s => wordConcatenation (σ a) (wordSubstitutionWord σ s)

noncomputable def wordSubstitution (σ : A → WordPolynomial k A) :
    WordPolynomial k A →ₗ[k] WordPolynomial k A :=
  Finsupp.linearCombination k (wordSubstitutionWord σ)

@[simp] theorem wordSubstitution_single (σ : A → WordPolynomial k A)
    (p : List A) (a : k) :
    wordSubstitution σ (Finsupp.single p a) = a • wordSubstitutionWord σ p := by
  classical
  simp [wordSubstitution]

theorem wordSubstitutionWord_append (σ : A → WordPolynomial k A) (p q : List A) :
    wordSubstitutionWord σ (p ++ q) =
      wordConcatenation (wordSubstitutionWord σ p) (wordSubstitutionWord σ q) := by
  induction p with
  | nil => simp [wordSubstitutionWord]
  | cons a p ih => simp only [List.cons_append, wordSubstitutionWord, ih,
      wordConcatenation_assoc]

theorem wordSubstitution_concatenation (σ : A → WordPolynomial k A)
    (f g : WordPolynomial k A) :
    wordSubstitution σ (wordConcatenation f g) =
      wordConcatenation (wordSubstitution σ f) (wordSubstitution σ g) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f f' hf hf' => simp only [map_add, LinearMap.add_apply, hf, hf']
  | single p a =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g g' hg hg' => simp only [map_add, hg, hg']
    | single q b => simp [wordSubstitutionWord_append, map_smul,
        LinearMap.smul_apply, smul_smul, mul_comm]

theorem cyclicTrace_wordSubstitutionWord_append_swap
    (σ : A → WordPolynomial k A) (p q : List A) :
    cyclicTrace (wordSubstitutionWord σ (p ++ q)) =
      cyclicTrace (wordSubstitutionWord σ (q ++ p)) := by
  simp only [wordSubstitutionWord_append]
  exact cyclicTrace_wordConcatenation_swap _ _

theorem cyclicTrace_wordSubstitutionWord_rotate
    (σ : A → WordPolynomial k A) (p : List A) (n : ℕ) :
    cyclicTrace (wordSubstitutionWord σ (p.rotate n)) =
      cyclicTrace (wordSubstitutionWord σ p) := by
  rw [List.rotate_eq_drop_append_take_mod,
    cyclicTrace_wordSubstitutionWord_append_swap, List.take_append_drop]

noncomputable def cyclicSubstitutionWord (σ : A → WordPolynomial k A) :
    CyclicWord A → CyclicPolynomial k A :=
  Quotient.lift (fun p => cyclicTrace (wordSubstitutionWord σ p)) (by
    rintro p p' ⟨n, rfl⟩
    exact (cyclicTrace_wordSubstitutionWord_rotate σ p n).symm)

noncomputable def cyclicSubstitution (σ : A → WordPolynomial k A) :
    CyclicPolynomial k A →ₗ[k] CyclicPolynomial k A :=
  Finsupp.linearCombination k (cyclicSubstitutionWord σ)

@[simp] theorem cyclicSubstitution_traceWord (σ : A → WordPolynomial k A) (p : List A) :
    cyclicSubstitution σ (traceWord p) = cyclicTrace (wordSubstitutionWord σ p) := by
  classical
  simp only [cyclicSubstitution, traceWord, Finsupp.linearCombination_single, one_smul]
  rfl

theorem cyclicSubstitution_cyclicTrace (σ : A → WordPolynomial k A)
    (f : WordPolynomial k A) :
    cyclicSubstitution σ (cyclicTrace f) = cyclicTrace (wordSubstitution σ f) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single p a => simp [cyclicTrace, map_smul]

end ASGinzburg
