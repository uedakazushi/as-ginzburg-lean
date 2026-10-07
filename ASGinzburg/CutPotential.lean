import ASGinzburg.CutQuiver
import Mathlib.Data.List.Rotate
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Cyclic words and the cut Euler identity

The cyclic vector space is a free vector space on words modulo rotation.
The statements in this file also apply to words that are not quiver paths;
restricting to closed, composable quiver paths is a separate task.
`cutReconstruction` sums [a · (the cyclic word with this occurrence of a
removed)] over cut occurrences. Thus it is the finite-word content of (3.8).
-/

namespace ASGinzburg

universe u v

variable {A : Type u} {k : Type v} [Field k]

abbrev CyclicWord (A : Type u) := Quotient (List.IsRotated.setoid A)
abbrev WordPolynomial (k : Type v) (A : Type u) [Field k] := List A →₀ k
abbrev CyclicPolynomial (k : Type v) (A : Type u) [Field k] := CyclicWord A →₀ k

def wordClass (w : List A) : CyclicWord A := Quotient.mk _ w

noncomputable def traceWord (w : List A) : CyclicPolynomial k A :=
  Finsupp.single (wordClass w) 1

theorem wordClass_append_swap (p q : List A) : wordClass (p ++ q) = wordClass (q ++ p) := by
  apply Quotient.sound
  exact ⟨p.length, List.rotate_append_length_eq p q⟩

theorem traceWord_append_swap (p q : List A) :
    traceWord (k := k) (p ++ q) = traceWord (q ++ p) := by
  simp only [traceWord, wordClass_append_swap p q]

def wordCutDegree (cut : A → Bool) : List A → ℕ
  | [] => 0
  | a :: w => (if cut a then 1 else 0) + wordCutDegree cut w

theorem wordCutDegree_append (cut : A → Bool) (p q : List A) :
    wordCutDegree cut (p ++ q) = wordCutDegree cut p + wordCutDegree cut q := by
  induction p with
  | nil => simp [wordCutDegree]
  | cons a p ih => simp [wordCutDegree, ih, Nat.add_assoc]

theorem unique_cut_split (cut : A → Bool) (w : List A)
    (hw : wordCutDegree cut w = 1) :
    ∃ p a q, w = p ++ a :: q ∧ cut a = true ∧
      wordCutDegree cut p = 0 ∧ wordCutDegree cut q = 0 := by
  induction w with
  | nil => simp [wordCutDegree] at hw
  | cons a w ih =>
    cases ha : cut a
    · simp only [wordCutDegree, ha, Bool.false_eq_true, ↓reduceIte, zero_add] at hw
      obtain ⟨p, b, q, hp, hb, hpd, hqd⟩ := ih hw
      refine ⟨a :: p, b, q, by simp [hp], hb, ?_, hqd⟩
      simp [wordCutDegree, ha, hpd]
    · refine ⟨[], a, w, rfl, ha, rfl, ?_⟩
      simp only [wordCutDegree, ha, ↓reduceIte] at hw
      omega

/-- Sum over cut occurrences. `pre` stores the already traversed letters. -/
noncomputable def reconstructAux (cut : A → Bool) (pre : List A) :
    List A → CyclicPolynomial k A
  | [] => 0
  | a :: suffix =>
      (if cut a then traceWord (a :: (suffix ++ pre)) else 0) +
        reconstructAux cut (pre ++ [a]) suffix

theorem reconstructAux_euler (cut : A → Bool) (pre suffix : List A) :
    reconstructAux (k := k) cut pre suffix =
      wordCutDegree cut suffix • traceWord (pre ++ suffix) := by
  induction suffix generalizing pre with
  | nil => simp [reconstructAux, wordCutDegree]
  | cons a suffix ih =>
    have hrot : traceWord (k := k) (a :: (suffix ++ pre)) =
        traceWord (pre ++ a :: suffix) := by
      simpa only [List.cons_append, List.nil_append] using
        traceWord_append_swap (k := k) (a :: suffix) pre
    simp only [reconstructAux, ih, List.append_assoc, List.singleton_append, wordCutDegree]
    cases cut a <;> simp [hrot, add_nsmul]

noncomputable def cyclicTrace : WordPolynomial k A →ₗ[k] CyclicPolynomial k A :=
  Finsupp.linearCombination k (traceWord (k := k))

noncomputable def cutReconstruction (cut : A → Bool) :
    WordPolynomial k A →ₗ[k] CyclicPolynomial k A :=
  Finsupp.linearCombination k (reconstructAux (k := k) cut [])

/-- A genuine equality of cyclic polynomials, without any AS or CY hypotheses. -/
theorem cut_euler_identity (cut : A → Bool) (φ : WordPolynomial k A)
    (hφ : ∀ w ∈ φ.support, wordCutDegree cut w = 1) :
    cutReconstruction cut φ = cyclicTrace φ := by
  classical
  simp only [cutReconstruction, cyclicTrace, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [reconstructAux_euler, hφ w hw]
  simp

theorem cut_normal_form (cut : A → Bool) (w : List A)
    (hw : wordCutDegree cut w = 1) :
    ∃ a r, cut a = true ∧ wordCutDegree cut r = 0 ∧ wordClass w = wordClass (a :: r) := by
  obtain ⟨p, a, q, hword, ha, hp, hq⟩ := unique_cut_split cut w hw
  refine ⟨a, q ++ p, ha, ?_, ?_⟩
  · simp [wordCutDegree_append, hp, hq]
  · rw [hword, wordClass_append_swap]
    rfl

theorem path_word_cutDegree (Q : CutQuiver) {u v : Q.Vertex} (p : Q.Path u v) :
    wordCutDegree Q.cut p.toList = p.cutDegree := by
  induction p with
  | nil => rfl
  | snoc p a h ih =>
    simp [CutQuiver.Path.toList, CutQuiver.Path.cutDegree,
      wordCutDegree_append, wordCutDegree, CutQuiver.cutDegree, ih]

end ASGinzburg
