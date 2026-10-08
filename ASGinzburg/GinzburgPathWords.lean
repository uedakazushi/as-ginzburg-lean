import ASGinzburg.GinzburgPathAlgebra
import ASGinzburg.PathWordEmbeddings

/-! The genuine extended paths embed injectively into words. Original
paths are exactly the cohomological degree zero basis paths. -/
namespace ASGinzburg.CutQuiver.GinzburgPath
variable {Q : CutQuiver}

theorem toList_sigma_injective (u : Q.Vertex) :
    Function.Injective (fun p : Σ v, Q.GinzburgPath u v => p.2.toList) := by
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
      have H := ih w q (List.reverse_injective hpq)
      cases H
      rfl

theorem toList_injective (u v : Q.Vertex) :
    Function.Injective (toList : Q.GinzburgPath u v → List Q.GinzburgArrow) := by
  intro p q h
  have H : (⟨v,p⟩ : Σ v, Q.GinzburgPath u v)=⟨v,q⟩ := toList_sigma_injective u h
  exact eq_of_heq (Sigma.mk.inj H).2

end ASGinzburg.CutQuiver.GinzburgPath

namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgPathWordMap (u v : Q.Vertex) :
    Q.GinzburgPathComponent k u v →ₗ[k] WordPolynomial k Q.GinzburgArrow :=
  Finsupp.lmapDomain k k GinzburgPath.toList

theorem ginzburgPathWordMap_injective (u v : Q.Vertex) :
    Function.Injective (Q.ginzburgPathWordMap k u v) :=
  Finsupp.mapDomain_injective (GinzburgPath.toList_injective u v)

theorem Path.originalGinzburg_toList {u v : Q.Vertex} (p : Q.Path u v) :
    (p.originalGinzburg Q).toList=p.toList.map GinzburgArrow.original := by
  induction p with
  | nil => simp [originalGinzburg,GinzburgPath.toList,Path.toList]
  | snoc p a h ih => simp [originalGinzburg,GinzburgPath.toList,Path.toList,ih]

theorem Path.originalGinzburg_injective (u v : Q.Vertex) :
    Function.Injective (Path.originalGinzburg Q (u:=u) (v:=v)) := by
  intro p q h
  have H := congrArg GinzburgPath.toList h
  rw [Path.originalGinzburg_toList,Path.originalGinzburg_toList] at H
  have hi : Function.Injective (GinzburgArrow.original (Q:=Q)) := by
    intro a b h
    exact GinzburgArrow.original.inj h
  exact Path.toList_injective u v ((List.map_injective_iff.mpr hi) H)

def degreeZeroGinzburgPaths (u v : Q.Vertex) := {p : Q.GinzburgPath u v //p.cohomologicalDegree=0}

noncomputable def originalPathEquivDegreeZero (u v : Q.Vertex) :
    Q.Path u v ≃ Q.degreeZeroGinzburgPaths u v :=
  Equiv.ofBijective (fun p => ⟨p.originalGinzburg Q,p.originalGinzburg_cohomologicalDegree Q⟩)
    ⟨by intro p q h; exact Path.originalGinzburg_injective Q u v (congrArg Subtype.val h),
      by
        rintro ⟨p,hp⟩
        obtain ⟨q,hq⟩ := p.degreeZero_existsOriginal Q hp
        exact ⟨q,Subtype.ext hq⟩⟩

end ASGinzburg.CutQuiver
