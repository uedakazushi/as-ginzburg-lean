import ASGinzburg.PathWordEmbeddings

/-! Actual composable prefixes and suffixes at every position of an
actual path. Nonempty closed arrow words determine their base vertex. -/
namespace ASGinzburg.CutQuiver.Path
variable {Q : CutQuiver}

theorem exists_split_at_length {i j : Q.Vertex} (p : Q.Path i j)
    (n : ℕ) (hn : n ≤ p.length) :
    ∃ m : Q.Vertex, ∃ a : Q.Path i m, ∃ b : Q.Path m j,
      a.length=n ∧ a.comp b=p := by
  induction p generalizing n with
  | nil =>
    have hn0 : n=0 := by simpa [length] using hn
    subst n
    exact ⟨i,.nil i,.nil i,rfl,rfl⟩
  | @snoc v p c hc ih =>
    by_cases hnp : n ≤ p.length
    · obtain ⟨m,a,b,ha,hcomp⟩ := ih n hnp
      exact ⟨m,a,.snoc b c hc,ha,by rw [comp,hcomp]⟩
    · have hn' : n=p.length+1 := by simp only [length] at hn; omega
      exact ⟨Q.target c,.snoc p c hc,.nil _,hn'.symm,rfl⟩

theorem target_of_toList_getLast {i j : Q.Vertex} (p : Q.Path i j)
    (a : Q.Arrow) (h : p.toList.getLast? = some a) : Q.target a=j := by
  cases p with
  | nil => simp [toList] at h
  | snoc p b hb =>
    have hba : b=a := by simpa [toList] using h
    subst a
    rfl

theorem closed_toList_base_eq {i j : Q.Vertex} (p : Q.Path i i) (q : Q.Path j j)
    (hp : 0 < p.length) (hword : p.toList=q.toList) : i=j := by
  cases p with
  | nil => simp [length] at hp
  | snoc p a ha =>
    have hlast : q.toList.getLast?=some a := by
      rw [← hword]
      simp [toList]
    exact q.target_of_toList_getLast a hlast

theorem closed_toList_sigma_eq (p q : Σ i : Q.Vertex, Q.Path i i)
    (hp : 0 < p.2.length) (hword : p.2.toList=q.2.toList) : p=q := by
  rcases p with ⟨i,p⟩
  rcases q with ⟨j,q⟩
  have hij := p.closed_toList_base_eq q hp hword
  subst j
  have hpq : p=q := toList_injective i i hword
  subst q
  rfl

end ASGinzburg.CutQuiver.Path
