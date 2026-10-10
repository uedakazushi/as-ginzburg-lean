import ASGinzburg.CyclicDerivative

/-! Genuine noncommutative concatenation of finite word polynomials. The
first factor supplies the prefix, and the second supplies the suffix. -/
namespace ASGinzburg
universe u v
variable {A : Type u} {k : Type v} [Field k]

noncomputable def wordConcatenation :
    WordPolynomial k A →ₗ[k] WordPolynomial k A →ₗ[k] WordPolynomial k A :=
  Finsupp.linearCombination k (fun p => Finsupp.lmapDomain k k (List.append p))

@[simp] theorem wordConcatenation_single (p q : List A) (a b : k) :
    wordConcatenation (Finsupp.single p a) (Finsupp.single q b) =
      Finsupp.single (p ++ q) (a * b) := by
  classical
  simp [wordConcatenation, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

@[simp] theorem wordConcatenation_unit_left (f : WordPolynomial k A) :
    wordConcatenation (Finsupp.single [] 1) f = f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [map_add, hf, hg]
  | single p a => simp

@[simp] theorem wordConcatenation_unit_right (f : WordPolynomial k A) :
    wordConcatenation f (Finsupp.single [] 1) = f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [map_add, LinearMap.add_apply, hf, hg]
  | single p a => simp

theorem wordConcatenation_assoc (f g h : WordPolynomial k A) :
    wordConcatenation (wordConcatenation f g) h =
      wordConcatenation f (wordConcatenation g h) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f f' hf hf' => simp [map_add, LinearMap.add_apply, hf, hf']
  | single p a =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g g' hg hg' => simp [map_add, LinearMap.add_apply, hg, hg']
    | single q b =>
      induction h using Finsupp.induction_linear with
      | zero => simp
      | add h h' hh hh' => simp only [map_add, hh, hh']
      | single r c => simp [List.append_assoc, mul_assoc]

theorem cyclicTrace_wordConcatenation_swap (f g : WordPolynomial k A) :
    cyclicTrace (wordConcatenation f g) = cyclicTrace (wordConcatenation g f) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f f' hf hf' => simp [map_add, LinearMap.add_apply, hf, hf']
  | single p a =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g g' hg hg' => simp [map_add, LinearMap.add_apply, hg, hg']
    | single q b => simp [cyclicTrace, traceWord_append_swap p q, mul_comm]

end ASGinzburg
