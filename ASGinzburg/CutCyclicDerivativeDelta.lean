import ASGinzburg.CyclicDerivative

/-! A cut-zero word contains no cut letter. Cyclic differentiation of
the word formed by one cut letter followed by a cut-zero word therefore
recovers precisely that word, and vanishes at other cut letters. -/
namespace ASGinzburg
universe u v
variable {A : Type u} [DecidableEq A] {k : Type v} [Field k]

theorem derivativeAux_eq_zero_of_cut_zero (cut : A → Bool) (a : A)
    (ha : cut a=true) (pre w : List A) (hw : wordCutDegree cut w=0) :
    derivativeAux (k:=k) a pre w=0 := by
  induction w generalizing pre with
  | nil => rfl
  | cons b w ih =>
    have hb : cut b=false := by
      cases hc : cut b
      · rfl
      · simp only [wordCutDegree,hc,↓reduceIte] at hw
        omega
    have ht : wordCutDegree cut w=0 := by simpa [wordCutDegree,hb] using hw
    have hab : a≠b := by
      intro hab
      have h := congrArg cut hab
      rw [ha,hb] at h
      contradiction
    simp only [derivativeAux,if_neg hab,zero_add]
    exact ih (pre++[b]) ht

theorem derivativeWord_cut_cons (cut : A → Bool) (a b : A)
    (hb : cut b=true) (w : List A) (hw : wordCutDegree cut w=0) :
    derivativeWord (k:=k) b (a::w)=if b=a then Finsupp.single w 1 else 0 := by
  simp only [derivativeWord,derivativeAux,List.append_nil]
  rw [derivativeAux_eq_zero_of_cut_zero cut b hb _ w hw,add_zero]

end ASGinzburg
