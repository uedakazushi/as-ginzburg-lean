import ASGinzburg.CyclicDerivativeCommutators

/-! The actual cyclic derivative's mixed coefficient identity follows
from its proved commutator identity, without any Hessian or Ext assumption. -/
namespace ASGinzburg
universe u v
variable {A : Type u} [DecidableEq A] [Fintype A] {k : Type v} [Field k]

omit [Fintype A] in
theorem prependWord_coeff (c a : A) (f : WordPolynomial k A) (w : List A) :
    prependWord c f (a::w) = if c=a then f w else 0 := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add,Finsupp.add_apply,hf,hg]
    split_ifs <;> simp
  | single l t =>
    by_cases h : c=a
    · subst c
      simp [prependWord,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,Finsupp.single_apply]
    · have hne : c::l ≠ a::w := by intro he; exact h (List.cons.inj he).1
      simp [prependWord,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,h,Ne.symm hne]

omit [Fintype A] in
theorem appendWord_coeff (c b : A) (f : WordPolynomial k A) (w : List A) :
    appendWord c f (w++[b]) = if c=b then f w else 0 := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add,Finsupp.add_apply,hf,hg]
    split_ifs <;> simp
  | single l t =>
    by_cases h : c=b
    · subst c
      simp [appendWord,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,Finsupp.single_apply]
    · have hne : l++[c] ≠ w++[b] := by
        intro he
        have hl := congrArg List.getLast? he
        exact h (by simpa using hl)
      simp [appendWord,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,h,Ne.symm hne]

theorem cyclicDerivative_mixed_coeff (φ : CyclicPolynomial k A)
    (a b : A) (w : List A) :
    cyclicDerivative a φ (w++[b]) = cyclicDerivative b φ (a::w) := by
  have h := congrArg (fun f : WordPolynomial k A => f (a::(w++[b])))
    (cyclicDerivative_commutator φ)
  simp only [wordCommutator,LinearMap.sub_apply,Finsupp.sub_apply,Finset.sum_sub_distrib] at h
  simp only [Finsupp.finset_sum_apply,prependWord_coeff] at h
  change (∑ c, if c=a then cyclicDerivative c φ (w++[b]) else 0) -
    (∑ c, appendWord c (cyclicDerivative c φ) ((a::w)++[b])) = 0 at h
  simp only [appendWord_coeff,
    Finset.sum_ite_eq',Finset.mem_univ,if_true] at h
  exact sub_eq_zero.mp h

end ASGinzburg
