import ASGinzburg.PathDegreeUnrolling

/-! Forgetting sheets does not identify distinct unrolled paths with
fixed endpoints. Hence lifting fixed-degree paths is an equivalence. -/
namespace ASGinzburg.CutQuiver
variable {Q : CutQuiver}

theorem UnrolledPath.erase_toList_injective (u v : Q.LiftVertex) :
    Function.Injective (fun p : Q.UnrolledPath u v => p.erase.toList) := by
  intro p
  induction p with
  | nil =>
    intro q h
    cases q with
    | nil => rfl
    | snoc a q => simp [erase,Path.toList] at h
  | snoc a p ih =>
    intro q h
    cases q with
    | nil => simp [erase,Path.toList] at h
    | snoc b q =>
      have hl : p.erase.toList++[a.val]=q.erase.toList++[b.val] := by
        simpa [erase,Path.toList] using h
      obtain ⟨hp,hab⟩ := List.append_inj' hl rfl
      have hab' : a=b := Subtype.ext (List.singleton_inj.mp hab)
      subst b
      exact congrArg (UnrolledPath.snoc a) (ih hp)

theorem UnrolledPath.unrollDegree_eraseDegree {u v : Q.Vertex} {m : ℤ} {d : ℕ}
    (p : Q.UnrolledPath (u,m) (v,m+(d:ℤ))) : Path.unrollDegree m p.eraseDegree=p := by
  apply UnrolledPath.erase_toList_injective
  change (Path.unrollDegree m p.eraseDegree).erase.toList=p.erase.toList
  rw [Path.unrollDegree_erase_toList]
  rfl

def Path.unrollDegreeEquiv (m : ℤ) (u v : Q.Vertex) (d : ℕ) :
    Path.CutDegreePath (Q:=Q) u v d ≃ Q.UnrolledPath (u,m) (v,m+(d:ℤ)) where
  toFun := Path.unrollDegree m
  invFun := UnrolledPath.eraseDegree
  left_inv := Path.eraseDegree_unrollDegree m
  right_inv := UnrolledPath.unrollDegree_eraseDegree

universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def unrollDegreeLinearEquiv (u v : Q.Vertex) (d : ℕ) (m : ℤ) :
    (Path.CutDegreePath (Q:=Q) u v d →₀ k) ≃ₗ[k]
      Q.UnrolledPathComponent k (u,m) (v,m+(d:ℤ)) :=
  Finsupp.domLCongr (Path.unrollDegreeEquiv m u v d)

@[simp] theorem unrollDegreeLinearEquiv_single (u v : Q.Vertex) (d : ℕ) (m : ℤ)
    (p : Path.CutDegreePath (Q:=Q) u v d) (a : k) :
    Q.unrollDegreeLinearEquiv k u v d m (Finsupp.single p a)=
      Finsupp.single (Path.unrollDegree m p) a := by
  simp [unrollDegreeLinearEquiv,Finsupp.domLCongr,Path.unrollDegreeEquiv]

end ASGinzburg.CutQuiver
