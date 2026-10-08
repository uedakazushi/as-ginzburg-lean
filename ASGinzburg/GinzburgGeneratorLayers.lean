import ASGinzburg.GinzburgGeneratorFiltrationBounds
import ASGinzburg.GinzburgAugmentationComplex

/-! The consecutive terms of the genuine last-generator filtration
split, as graded vector spaces, by the exact degree of the last generator. -/
namespace ASGinzburg.CutQuiver
variable (Q : CutQuiver)

theorem GinzburgLastGeneratorData.path_injective (u v : Q.Vertex) :
    Function.Injective (GinzburgLastGeneratorData.path Q (u:=u) (v:=v)) := by
  intro d e h
  apply (Q.ginzburgNonemptyLastEquiv u v).symm.injective
  exact Subtype.ext h

def ginzburgGeneratorLayerPaths (u v : Q.Vertex) (r : ℤ) : Set (Q.GinzburgPath u v) :=
  {p | ∃ d : Q.GinzburgLastGeneratorData u v,
    d.path Q=p ∧ d.1.val.cohomologicalDegree Q=r}

theorem ginzburgGeneratorLayerPaths_le_filtration (u v : Q.Vertex) (r : ℤ) :
    Q.ginzburgGeneratorLayerPaths u v r ⊆ Q.ginzburgGeneratorFiltrationPaths u v r := by
  rintro p ⟨d,rfl,hd⟩
  exact ⟨d,rfl,le_of_eq hd.symm⟩

theorem ginzburgGeneratorFiltrationPaths_step (u v : Q.Vertex) (r : ℤ) :
    Q.ginzburgGeneratorFiltrationPaths u v r=
      Q.ginzburgGeneratorFiltrationPaths u v (r+1) ∪ Q.ginzburgGeneratorLayerPaths u v r := by
  ext p
  constructor
  · rintro ⟨d,rfl,hd⟩
    by_cases he : d.1.val.cohomologicalDegree Q=r
    · exact Or.inr ⟨d,rfl,he⟩
    · exact Or.inl ⟨d,rfl,by omega⟩
  · rintro (hp|hp)
    · exact Q.ginzburgGeneratorFiltrationPaths_antitone (by omega) hp
    · exact Q.ginzburgGeneratorLayerPaths_le_filtration u v r hp

theorem ginzburgGeneratorLayerPaths_disjoint (u v : Q.Vertex) (r : ℤ) :
    Disjoint (Q.ginzburgGeneratorFiltrationPaths u v (r+1))
      (Q.ginzburgGeneratorLayerPaths u v r) := by
  apply Set.disjoint_left.mpr
  rintro p ⟨d,hd,hr⟩ ⟨e,he,hs⟩
  have hde := GinzburgLastGeneratorData.path_injective Q u v (hd.trans he.symm)
  subst e
  omega

universe u
variable (k : Type u) [Field k]

def ginzburgGeneratorLayer (u v : Q.Vertex) (r : ℤ) :
    Submodule k (Q.GinzburgPathComponent k u v) :=
  Finsupp.supported k k (Q.ginzburgGeneratorLayerPaths u v r)

def ginzburgGeneratorFiltrationAtDegree (u v : Q.Vertex) (r q c : ℤ) :
    Submodule k (Q.GinzburgPathComponent k u v) :=
  Finsupp.supported k k {p | p ∈ Q.ginzburgGeneratorFiltrationPaths u v r ∧
    p.cohomologicalDegree=q ∧ p.cutDegree=c}

def ginzburgGeneratorLayerAtDegree (u v : Q.Vertex) (r q c : ℤ) :
    Submodule k (Q.GinzburgPathComponent k u v) :=
  Finsupp.supported k k {p | p ∈ Q.ginzburgGeneratorLayerPaths u v r ∧
    p.cohomologicalDegree=q ∧ p.cutDegree=c}

theorem ginzburgGeneratorFiltrationAtDegree_eq_inf (u v : Q.Vertex) (r q c : ℤ) :
    Q.ginzburgGeneratorFiltrationAtDegree k u v r q c=
      Q.ginzburgGeneratorFiltration k u v r ⊓ Q.ginzburgCutCohomologicalComponent k u v q c := by
  unfold ginzburgGeneratorFiltrationAtDegree ginzburgGeneratorFiltration
    ginzburgCutCohomologicalComponent ginzburgCohomologicalComponent ginzburgCutComponent
  rw [←Finsupp.supported_inter,←Finsupp.supported_inter]
  rfl

theorem ginzburgGeneratorLayerAtDegree_eq_inf (u v : Q.Vertex) (r q c : ℤ) :
    Q.ginzburgGeneratorLayerAtDegree k u v r q c=
      Q.ginzburgGeneratorLayer k u v r ⊓ Q.ginzburgCutCohomologicalComponent k u v q c := by
  unfold ginzburgGeneratorLayerAtDegree ginzburgGeneratorLayer
    ginzburgCutCohomologicalComponent ginzburgCohomologicalComponent ginzburgCutComponent
  rw [←Finsupp.supported_inter,←Finsupp.supported_inter]
  rfl

theorem ginzburgGeneratorFiltration_step (u v : Q.Vertex) (r : ℤ) :
    Q.ginzburgGeneratorFiltration k u v r=
      Q.ginzburgGeneratorFiltration k u v (r+1) ⊔ Q.ginzburgGeneratorLayer k u v r := by
  unfold ginzburgGeneratorFiltration ginzburgGeneratorLayer
  rw [Q.ginzburgGeneratorFiltrationPaths_step,Finsupp.supported_union]

theorem ginzburgGeneratorLayer_disjoint (u v : Q.Vertex) (r : ℤ) :
    Disjoint (Q.ginzburgGeneratorFiltration k u v (r+1))
      (Q.ginzburgGeneratorLayer k u v r) :=
  Finsupp.disjoint_supported_supported (Q.ginzburgGeneratorLayerPaths_disjoint u v r)

theorem ginzburgGeneratorFiltrationAtDegree_negTwo (u v : Q.Vertex) (q c : ℤ) :
    Q.ginzburgGeneratorFiltrationAtDegree k u v (-2) q c=
      Q.ginzburgAugmentationAtDegree k u v q c := by
  rw [Q.ginzburgGeneratorFiltrationAtDegree_eq_inf,Q.ginzburgGeneratorFiltration_negTwo,
    Q.ginzburgAugmentationAtDegree_eq_inf]

theorem ginzburgGeneratorFiltrationAtDegree_one (u v : Q.Vertex) (q c : ℤ) :
    Q.ginzburgGeneratorFiltrationAtDegree k u v 1 q c=⊥ := by
  rw [Q.ginzburgGeneratorFiltrationAtDegree_eq_inf,Q.ginzburgGeneratorFiltration_one,bot_inf_eq]

end ASGinzburg.CutQuiver
