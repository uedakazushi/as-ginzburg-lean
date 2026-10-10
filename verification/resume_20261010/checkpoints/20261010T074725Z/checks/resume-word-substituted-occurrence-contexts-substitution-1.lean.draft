import ASGinzburg.WordPolynomialSubstitution

/-! Finite word substitutions between distinct alphabets. The construction
uses actual concatenation and agrees with the existing one-alphabet action. -/
namespace ASGinzburg

universe u v w x
variable {A : Type u} {B : Type v} {C : Type w} {k : Type x} [Field k]

noncomputable def wordSubstitutionBetweenWord (σ : A → WordPolynomial k B) :
    List A → WordPolynomial k B
  | [] => Finsupp.single [] 1
  | a :: s => wordConcatenation (σ a) (wordSubstitutionBetweenWord σ s)

noncomputable def wordSubstitutionBetween (σ : A → WordPolynomial k B) :
    WordPolynomial k A →ₗ[k] WordPolynomial k B :=
  Finsupp.linearCombination k (wordSubstitutionBetweenWord σ)

@[simp] theorem wordSubstitutionBetween_single (σ : A → WordPolynomial k B)
    (p : List A) (a : k) :
    wordSubstitutionBetween σ (Finsupp.single p a) =
      a • wordSubstitutionBetweenWord σ p := by
  classical
  simp [wordSubstitutionBetween]

theorem wordSubstitutionBetweenWord_append (σ : A → WordPolynomial k B)
    (p q : List A) :
    wordSubstitutionBetweenWord σ (p ++ q) =
      wordConcatenation (wordSubstitutionBetweenWord σ p)
        (wordSubstitutionBetweenWord σ q) := by
  induction p with
  | nil => simp [wordSubstitutionBetweenWord]
  | cons a p ih => simp only [List.cons_append, wordSubstitutionBetweenWord, ih,
      wordConcatenation_assoc]

theorem wordSubstitutionBetween_concatenation (σ : A → WordPolynomial k B)
    (f g : WordPolynomial k A) :
    wordSubstitutionBetween σ (wordConcatenation f g) =
      wordConcatenation (wordSubstitutionBetween σ f)
        (wordSubstitutionBetween σ g) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f f' hf hf' => simp only [map_add, LinearMap.add_apply, hf, hf']
  | single p a =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g g' hg hg' => simp only [map_add, hg, hg']
    | single q b => simp [wordSubstitutionBetweenWord_append, map_smul,
        LinearMap.smul_apply, smul_smul, mul_comm]

theorem wordSubstitutionBetweenWord_same (σ : A → WordPolynomial k A)
    (p : List A) :
    wordSubstitutionBetweenWord σ p = wordSubstitutionWord σ p := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [wordSubstitutionBetweenWord, wordSubstitutionWord, ih]

theorem wordSubstitutionBetween_same (σ : A → WordPolynomial k A) :
    wordSubstitutionBetween σ = wordSubstitution σ := by
  apply Finsupp.lhom_ext'
  intro p
  apply LinearMap.ext_ring
  simp [wordSubstitutionBetweenWord_same]

theorem wordSubstitutionBetweenWord_composition (σ : A → WordPolynomial k B)
    (τ : B → WordPolynomial k C) (p : List A) :
    wordSubstitutionBetween τ (wordSubstitutionBetweenWord σ p) =
      wordSubstitutionBetweenWord (fun a => wordSubstitutionBetween τ (σ a)) p := by
  induction p with
  | nil => simp [wordSubstitutionBetweenWord]
  | cons a p ih =>
    simp only [wordSubstitutionBetweenWord, wordSubstitutionBetween_concatenation, ih]

theorem wordSubstitutionBetween_composition (σ : A → WordPolynomial k B)
    (τ : B → WordPolynomial k C) (f : WordPolynomial k A) :
    wordSubstitutionBetween τ (wordSubstitutionBetween σ f) =
      wordSubstitutionBetween (fun a => wordSubstitutionBetween τ (σ a)) f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single p a => simp [map_smul, wordSubstitutionBetweenWord_composition]

end ASGinzburg
