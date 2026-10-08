import ASGinzburg.PathUnrolling
import ASGinzburg.UnrolledPathAlgebra

/-! Fixed cut-degree path spaces lift injectively to fixed unrolled
components. Forgetting sheets recovers the actual arrow word. -/
namespace ASGinzburg.CutQuiver
variable {Q : CutQuiver}

abbrev Path.CutDegreePath (u v : Q.Vertex) (d : ℕ) := {p : Q.Path u v //p.cutDegree=d}

def Path.unrollDegree (m : ℤ) {u v : Q.Vertex} {d : ℕ}
    (p : CutDegreePath (Q:=Q) u v d) : Q.UnrolledPath (u,m) (v,m+(d:ℤ)) :=
  (p.val.unroll m).transport rfl (by rw [p.property])

theorem Path.unrollDegree_erase_toList (m : ℤ) {u v : Q.Vertex} {d : ℕ}
    (p : CutDegreePath (Q:=Q) u v d) :
    (Path.unrollDegree m p).erase.toList=p.val.toList := by
  simp [unrollDegree,unroll_erase_toList]

theorem Path.unrollDegree_injective (m : ℤ) (u v : Q.Vertex) (d : ℕ) :
    Function.Injective (unrollDegree (Q:=Q) m (u:=u) (v:=v) (d:=d)) := by
  intro p q h
  have H := congrArg (fun p : Q.UnrolledPath (u,m) (v,m+(d:ℤ)) => p.erase.toList) h
  simp only [unrollDegree_erase_toList] at H
  exact Subtype.ext (toList_injective u v H)

def UnrolledPath.eraseDegree {u v : Q.Vertex} {m : ℤ} {d : ℕ}
    (p : Q.UnrolledPath (u,m) (v,m+(d:ℤ))) : Path.CutDegreePath (Q:=Q) u v d :=
  ⟨p.erase,by
    have H := p.erase_cutDegree
    have hc : (p.erase.cutDegree:ℤ)=(d:ℤ) := by simpa using H
    exact_mod_cast hc⟩

theorem Path.eraseDegree_unrollDegree (m : ℤ) {u v : Q.Vertex} {d : ℕ}
    (p : CutDegreePath (Q:=Q) u v d) : (Path.unrollDegree m p).eraseDegree=p := by
  apply Subtype.ext
  apply toList_injective u v
  exact Path.unrollDegree_erase_toList m p

universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def unrollDegreeLinearMap (u v : Q.Vertex) (d : ℕ) (m : ℤ) :
    (Path.CutDegreePath (Q:=Q) u v d →₀ k) →ₗ[k]
      Q.UnrolledPathComponent k (u,m) (v,m+(d:ℤ)) :=
  Finsupp.lmapDomain k k (Path.unrollDegree m)

theorem unrollDegreeLinearMap_injective (u v : Q.Vertex) (d : ℕ) (m : ℤ) :
    Function.Injective (Q.unrollDegreeLinearMap k u v d m) :=
  Finsupp.mapDomain_injective (Path.unrollDegree_injective m u v d)

end ASGinzburg.CutQuiver
