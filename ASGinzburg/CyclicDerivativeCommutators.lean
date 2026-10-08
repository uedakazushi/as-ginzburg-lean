import ASGinzburg.CyclicDerivative

/-! The exact cyclic commutator identity needed for the square of the
Ginzburg loop differential. No differential or regularity is assumed. -/
namespace ASGinzburg
universe u v
variable {A : Type u} [DecidableEq A] [Fintype A] {k : Type v} [Field k]

noncomputable def prependWord (a : A) : WordPolynomial k A →ₗ[k] WordPolynomial k A :=
  Finsupp.lmapDomain k k (List.cons a)

noncomputable def appendWord (a : A) : WordPolynomial k A →ₗ[k] WordPolynomial k A :=
  Finsupp.lmapDomain k k (fun w => w++[a])

noncomputable def wordCommutator (a : A) : WordPolynomial k A →ₗ[k] WordPolynomial k A :=
  prependWord a-appendWord a

omit [DecidableEq A] [Fintype A] in
@[simp] theorem wordCommutator_single (a : A) (w : List A) (c : k) :
    wordCommutator a (Finsupp.single w c)=
      Finsupp.single (a::w) c-Finsupp.single (w++[a]) c := by
  simp [wordCommutator,prependWord,appendWord,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]

theorem derivativeAux_commutator (aPre suffix : List A) :
    (∑ a : A, wordCommutator a (derivativeAux (k:=k) a aPre suffix)) =
      Finsupp.single (suffix++aPre) 1-Finsupp.single (aPre++suffix) 1 := by
  induction suffix generalizing aPre with
  | nil => simp [derivativeAux]
  | cons b suffix ih =>
    have hterm (a : A) :
        wordCommutator a (derivativeAux (k:=k) a aPre (b::suffix)) =
        (if a=b then Finsupp.single (b::(suffix++aPre)) 1-
          Finsupp.single ((suffix++aPre)++[b]) 1 else 0)+
            wordCommutator a (derivativeAux a (aPre++[b]) suffix) := by
      by_cases hab : a=b <;> simp [derivativeAux,hab]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib,ih]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true,List.append_assoc,
      List.cons_append]
    abel

theorem derivativeWord_commutator (w : List A) :
    (∑ a : A, wordCommutator a (derivativeWord (k:=k) a w))=0 := by
  simpa only [List.append_nil,List.nil_append,sub_self] using
    derivativeAux_commutator (k:=k) [] w

theorem cyclicDerivative_commutator (φ : CyclicPolynomial k A) :
    (∑ a : A, wordCommutator a (cyclicDerivative a φ))=0 := by
  classical
  induction φ using Finsupp.induction_linear with
  | zero => simp
  | add φ ψ hφ hψ => simp [map_add,Finset.sum_add_distrib,hφ,hψ]
  | single c x =>
    obtain ⟨w,rfl⟩ := Quotient.exists_rep c
    change (∑ a, wordCommutator a
      (cyclicDerivative a (Finsupp.single (wordClass w) x)))=0
    simp only [cyclicDerivative,Finsupp.linearCombination_single,map_smul,
      derivativeCyclicWord_mk,←Finset.smul_sum,derivativeWord_commutator,smul_zero]

end ASGinzburg
