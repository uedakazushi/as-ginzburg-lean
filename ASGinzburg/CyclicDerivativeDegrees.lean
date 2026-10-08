import ASGinzburg.CyclicDerivative
import Mathlib.LinearAlgebra.Finsupp.Supported

/-! Cyclic differentiation removes exactly one letter and its cut degree. -/
namespace ASGinzburg
universe u v
variable {A : Type u} [DecidableEq A] {k : Type v} [Field k]

theorem derivativeAux_supported_degrees (cut : A → Bool) (a : A) (pre suffix : List A) :
    derivativeAux (k:=k) a pre suffix ∈ Finsupp.supported k k
      {w | w.length+1=pre.length+suffix.length ∧
        wordCutDegree cut w+(if cut a then 1 else 0)=
          wordCutDegree cut pre+wordCutDegree cut suffix} := by
  induction suffix generalizing pre with
  | nil => simp [derivativeAux]
  | cons b suffix ih =>
    rw [derivativeAux]
    apply Submodule.add_mem
    · by_cases hab : a=b
      · subst b
        rw [if_pos rfl]
        apply Finsupp.single_mem_supported
        constructor
        · simp only [List.length_append,List.length_cons]
          omega
        · simp only [wordCutDegree_append,wordCutDegree]
          omega
      · rw [if_neg hab]
        exact Submodule.zero_mem _
    · simpa [wordCutDegree_append,wordCutDegree,Nat.add_assoc,Nat.add_comm,
        Nat.add_left_comm] using ih (pre++[b])

theorem derivativeWord_supported_degrees (cut : A → Bool) (a : A) (w : List A) :
    derivativeWord (k:=k) a w ∈ Finsupp.supported k k
      {r | r.length+1=w.length ∧
        wordCutDegree cut r+(if cut a then 1 else 0)=wordCutDegree cut w} := by
  simpa only [List.length_nil,zero_add,wordCutDegree] using
    derivativeAux_supported_degrees (k:=k) cut a [] w

end ASGinzburg
