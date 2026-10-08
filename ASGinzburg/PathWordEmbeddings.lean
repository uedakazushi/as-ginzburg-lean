import ASGinzburg.PathAlgebra

/-! A composable path is determined by its initial vertex and actual arrow
word, including for parallel arrows. -/
namespace ASGinzburg.CutQuiver.Path
variable {Q : CutQuiver}

theorem toList_comp {u v w : Q.Vertex} (p : Q.Path u v) (q : Q.Path v w) :
    (p.comp q).toList=p.toList++q.toList := by
  induction q with
  | nil => simp [comp,toList]
  | snoc q a h ih => simp [comp,toList,ih,List.append_assoc]

theorem toList_sigma_injective (u : Q.Vertex) :
    Function.Injective (fun p : Σ v, Q.Path u v => p.2.toList) := by
  rintro ⟨v,p⟩ ⟨w,q⟩ hword
  induction p generalizing w with
  | nil =>
    cases q with
    | nil => rfl
    | snoc q a h => simp [toList] at hword
  | @snoc v p a h ih =>
    cases q with
    | nil => simp [toList] at hword
    | @snoc w q b hb =>
      have hr := congrArg List.reverse hword
      simp only [toList,List.reverse_append,List.reverse_singleton,List.singleton_append] at hr
      obtain ⟨hab,hpq⟩ := List.cons.inj hr
      subst b
      have hpq' := List.reverse_injective hpq
      have H := ih w q hpq'
      cases H
      rfl

theorem toList_injective (u v : Q.Vertex) :
    Function.Injective (toList : Q.Path u v → List Q.Arrow) := by
  intro p q h
  have H : (⟨v,p⟩ : Σ v, Q.Path u v)=⟨v,q⟩ := toList_sigma_injective u h
  exact eq_of_heq (Sigma.mk.inj H).2

end ASGinzburg.CutQuiver.Path

namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def pathWordMap (u v : Q.Vertex) :
    Q.PathComponent k u v →ₗ[k] WordPolynomial k Q.Arrow :=
  Finsupp.lmapDomain k k Path.toList

theorem pathWordMap_injective (u v : Q.Vertex) :
    Function.Injective (Q.pathWordMap k u v) :=
  Finsupp.mapDomain_injective (Path.toList_injective u v)

end ASGinzburg.CutQuiver
