import ASGinzburg.CutPotential

/-!
# Actual cyclic derivatives and reconstruction

Cyclic differentiation is defined on the rotation quotient and proved
independent of representatives. The cut reconstruction operator is then
identified with the sum of a times its cyclic derivative, as in (3.8).
-/

namespace ASGinzburg

universe u v
variable {A : Type u} [DecidableEq A] {k : Type v} [Field k]

noncomputable def derivativeAux (a : A) (pre : List A) : List A → WordPolynomial k A
  | [] => 0
  | b :: suffix =>
      (if a = b then Finsupp.single (suffix ++ pre) 1 else 0) +
        derivativeAux a (pre ++ [b]) suffix

noncomputable def derivativeWord (a : A) (w : List A) : WordPolynomial k A :=
  derivativeAux a [] w

theorem derivativeAux_append (a : A) (pre p q : List A) :
    derivativeAux (k := k) a pre (p ++ q) =
      derivativeAux a (q ++ pre) p + derivativeAux a (pre ++ p) q := by
  induction p generalizing pre with
  | nil => simp [derivativeAux]
  | cons b p ih =>
    simp only [List.cons_append, derivativeAux, ih]
    simp [List.append_assoc, add_assoc]

theorem derivativeWord_append_swap (a : A) (p q : List A) :
    derivativeWord (k := k) a (p ++ q) = derivativeWord a (q ++ p) := by
  simp only [derivativeWord, derivativeAux_append, List.append_nil, List.nil_append]
  exact add_comm _ _

theorem derivativeWord_rotate (a : A) (w : List A) (n : ℕ) :
    derivativeWord (k := k) a (w.rotate n) = derivativeWord a w := by
  rw [List.rotate_eq_drop_append_take_mod, derivativeWord_append_swap,
    List.take_append_drop]

noncomputable def derivativeCyclicWord (a : A) : CyclicWord A → WordPolynomial k A :=
  Quotient.lift (derivativeWord a) (by
    rintro w w' ⟨n, rfl⟩
    exact (derivativeWord_rotate a w n).symm)

@[simp] theorem derivativeCyclicWord_mk (a : A) (w : List A) :
    derivativeCyclicWord (k := k) a (wordClass w) = derivativeWord a w := rfl

noncomputable def cyclicDerivative (a : A) :
    CyclicPolynomial k A →ₗ[k] WordPolynomial k A :=
  Finsupp.linearCombination k (derivativeCyclicWord a)

noncomputable def prependTrace (a : A) :
    WordPolynomial k A →ₗ[k] CyclicPolynomial k A :=
  Finsupp.linearCombination k (fun w => traceWord (a :: w))

omit [DecidableEq A] in
@[simp] theorem prependTrace_single (a : A) (w : List A) (c : k) :
    prependTrace a (Finsupp.single w c) = c • traceWord (a :: w) := by
  simp [prependTrace]

@[simp] theorem cyclicDerivative_traceWord (a : A) (w : List A) :
    cyclicDerivative a (traceWord (k := k) w) = derivativeWord a w := by
  simp [cyclicDerivative, traceWord]

section Finite

variable [Fintype A]

theorem derivativeAux_reconstruction (cut : A → Bool) (pre suffix : List A) :
    (∑ a, if cut a then prependTrace a (derivativeAux (k := k) a pre suffix) else 0) =
      reconstructAux cut pre suffix := by
  classical
  induction suffix generalizing pre with
  | nil => simp [derivativeAux, reconstructAux]
  | cons b suffix ih =>
    have hterm : ∀ a : A,
        (if cut a then prependTrace (k := k) a (derivativeAux a pre (b :: suffix)) else 0) =
          (if a = b then (if cut a then traceWord (k := k) (a :: (suffix ++ pre)) else 0) else 0) +
            (if cut a then prependTrace (k := k) a (derivativeAux a (pre ++ [b]) suffix) else 0) := by
      intro a
      by_cases hab : a = b <;> cases cut a <;>
        simp [derivativeAux, hab]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, ih]
    simp [reconstructAux]

noncomputable def cyclicCutReconstruction (cut : A → Bool) :
    CyclicPolynomial k A →ₗ[k] CyclicPolynomial k A :=
  ∑ a, if cut a then (prependTrace a).comp (cyclicDerivative a) else 0

theorem ite_linearMap_apply {M N : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] (p : Prop) [Decidable p]
    (f g : M →ₗ[k] N) (x : M) : (if p then f else g) x = if p then f x else g x := by
  split_ifs <;> rfl

theorem cyclicCutReconstruction_traceWord (cut : A → Bool) (w : List A) :
    cyclicCutReconstruction cut (traceWord (k := k) w) = reconstructAux cut [] w := by
  simp only [cyclicCutReconstruction, LinearMap.sum_apply, ite_linearMap_apply,
    LinearMap.comp_apply, cyclicDerivative_traceWord, LinearMap.zero_apply, derivativeWord]
  exact derivativeAux_reconstruction cut [] w

theorem cyclicCutReconstruction_comp_trace (cut : A → Bool) :
    (cyclicCutReconstruction (k := k) cut).comp cyclicTrace = cutReconstruction cut := by
  apply Finsupp.lhom_ext
  intro w c
  simp [cyclicTrace, cutReconstruction, cyclicCutReconstruction_traceWord]

/-- Equation (3.8) for any finite polynomial representative of cut degree one. -/
theorem cut_cyclic_derivative_identity (cut : A → Bool) (φ : WordPolynomial k A)
    (hφ : ∀ w ∈ φ.support, wordCutDegree cut w = 1) :
    (∑ a, if cut a then prependTrace a (cyclicDerivative a (cyclicTrace φ)) else 0) =
      cyclicTrace φ := by
  have h := LinearMap.congr_fun (cyclicCutReconstruction_comp_trace (k := k) cut) φ
  simp only [LinearMap.comp_apply, cyclicCutReconstruction, LinearMap.sum_apply,
    ite_linearMap_apply, LinearMap.zero_apply, LinearMap.comp_apply] at h
  rw [h]
  exact cut_euler_identity cut φ hφ

end Finite
end ASGinzburg
