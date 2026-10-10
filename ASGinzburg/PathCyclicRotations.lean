import ASGinzburg.PathCyclicClasses
import ASGinzburg.PathSplitting

/-! All actual nonempty closed paths representing one cyclic word have
one and the same class in the actual cyclic quotient of the path algebra. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem closedPathCyclicClass_eq_of_rotated (i j : Q.Vertex)
    (p : Q.Path i i) (q : Q.Path j j) (hp : 0 < p.length)
    (h : List.IsRotated p.toList q.toList) :
    Q.closedPathCyclicClass k i (Finsupp.single p 1) =
      Q.closedPathCyclicClass k j (Finsupp.single q 1) := by
  obtain ⟨n,hn⟩ := h
  obtain ⟨m,a,b,ha,hcomp⟩ := p.exists_split_at_length (n % p.length)
    (Nat.mod_lt n hp).le
  have hword : p.toList=a.toList++b.toList := by rw [← hcomp,Path.toList_comp]
  have hrot : p.toList.rotate n=(b.comp a).toList := by
    calc
      p.toList.rotate n = p.toList.rotate (n % p.length) := by
        rw [← p.length_toList]
        exact (List.rotate_mod p.toList n).symm
      _ = (b.comp a).toList := by
        rw [hword,← ha,← a.length_toList,List.rotate_append_length_eq,Path.toList_comp]
  have hlen : (b.comp a).length=p.length := by
    rw [← (b.comp a).length_toList,← hrot,List.length_rotate,p.length_toList]
  have hq : (⟨m,b.comp a⟩ : Σ t : Q.Vertex, Q.Path t t)=⟨j,q⟩ :=
    Path.closed_toList_sigma_eq _ _ (by simpa only [hlen] using hp) (hrot.symm.trans hn)
  have hclass : Q.closedPathCyclicClass k i (Finsupp.single p 1) =
      Q.closedPathCyclicClass k m (Finsupp.single (b.comp a) 1) := by
    rw [← hcomp]
    exact Q.closedPathCyclicClass_rotate_split k i m a b
  exact hclass.trans (congrArg
    (fun t : Σ s : Q.Vertex, Q.Path s s =>
      Q.closedPathCyclicClass k t.1 (Finsupp.single t.2 1)) hq)

theorem closedPathCyclicClass_eq_of_wordClass (i j : Q.Vertex)
    (p : Q.Path i i) (q : Q.Path j j) (hp : 0 < p.length)
    (h : wordClass p.toList=wordClass q.toList) :
    Q.closedPathCyclicClass k i (Finsupp.single p 1) =
      Q.closedPathCyclicClass k j (Finsupp.single q 1) :=
  Q.closedPathCyclicClass_eq_of_rotated k i j p q hp (Quotient.exact h)

end ASGinzburg.CutQuiver
