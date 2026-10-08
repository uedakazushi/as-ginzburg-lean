import ASGinzburg.GinzburgAugmentationIdeal
import ASGinzburg.GinzburgLastGeneratorGradings

/-! The genuine last-generator filtration of the free augmentation
module, which has exactly the original, dual and loop layers. -/
namespace ASGinzburg.CutQuiver
variable (Q : CutQuiver)

def ginzburgGeneratorFiltrationPaths (u v : Q.Vertex) (r : ℤ) : Set (Q.GinzburgPath u v) :=
  {p | ∃ d : Q.GinzburgLastGeneratorData u v, d.path Q=p ∧ r≤d.1.val.cohomologicalDegree Q}

theorem ginzburgGeneratorFiltrationPaths_nonempty {u v : Q.Vertex} {r : ℤ}
    {p : Q.GinzburgPath u v} (hp : p ∈ Q.ginzburgGeneratorFiltrationPaths u v r) :
    0<p.length := by
  obtain ⟨d,rfl,hd⟩ := hp
  rw [d.path_length]
  omega

theorem ginzburgGeneratorFiltrationPaths_of_degree {u v : Q.Vertex}
    {p : Q.GinzburgPath u v} (hp : 0<p.length) (r : ℤ) (hr : r≤p.cohomologicalDegree) :
    p ∈ Q.ginzburgGeneratorFiltrationPaths u v r := by
  let d := p.lastGenerator Q hp
  refine ⟨d,p.lastGenerator_path Q hp,?_⟩
  have hn := d.2.cohomologicalDegree_nonpos
  have he : p.cohomologicalDegree=d.2.cohomologicalDegree+d.1.val.cohomologicalDegree Q := by
    rw [←p.lastGenerator_path Q hp]
    exact d.path_cohomologicalDegree Q
  omega

theorem ginzburgGeneratorFiltrationPaths_comp {u v w : Q.Vertex}
    (p : Q.GinzburgPath u v) {q : Q.GinzburgPath v w} {r : ℤ}
    (hq : q ∈ Q.ginzburgGeneratorFiltrationPaths v w r) :
    p.comp q ∈ Q.ginzburgGeneratorFiltrationPaths u w r := by
  obtain ⟨⟨⟨a,ha⟩,s⟩,rfl,hr⟩ := hq
  cases ha
  refine ⟨⟨⟨a,rfl⟩,p.comp s⟩,?_,hr⟩
  rfl

universe u
variable (k : Type u) [Field k]

def ginzburgGeneratorFiltration (u v : Q.Vertex) (r : ℤ) :
    Submodule k (Q.GinzburgPathComponent k u v) :=
  Finsupp.supported k k (Q.ginzburgGeneratorFiltrationPaths u v r)

theorem ginzburgGeneratorFiltration_le_augmentation (u v : Q.Vertex) (r : ℤ) :
    Q.ginzburgGeneratorFiltration k u v r ≤ Q.ginzburgAugmentationSubmodule k u v :=
  Finsupp.supported_mono (fun _p hp => Q.ginzburgGeneratorFiltrationPaths_nonempty hp)

theorem ginzburgGeneratorFiltration_comp {u v w : Q.Vertex} {r : ℤ}
    {g : Q.GinzburgPathComponent k v w} (hg : g ∈ Q.ginzburgGeneratorFiltration k v w r)
    (f : Q.GinzburgPathComponent k u v) :
    Q.ginzburgPathComp k g f ∈ Q.ginzburgGeneratorFiltration k u w r := by
  apply Q.ginzburgSupported_comp k Set.univ (Q.ginzburgGeneratorFiltrationPaths v w r)
    (Q.ginzburgGeneratorFiltrationPaths u w r) _
      (by rw [Finsupp.supported_univ]; trivial) hg
  intro p _hp q hq
  exact Q.ginzburgGeneratorFiltrationPaths_comp p hq

end ASGinzburg.CutQuiver
