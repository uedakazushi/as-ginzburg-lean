import ASGinzburg.GinzburgGeneratorFiltration

/-! The actual signed differential preserves the genuine three-layer
last-generator filtration and raises the generator layer on generators. -/
namespace ASGinzburg.CutQuiver
variable (Q : CutQuiver)

theorem ginzburgGeneratorFiltrationPaths_antitone {u v : Q.Vertex} {r s : ℤ} (hrs : r≤s) :
    Q.ginzburgGeneratorFiltrationPaths u v s ⊆ Q.ginzburgGeneratorFiltrationPaths u v r := by
  rintro p ⟨d,rfl,hd⟩
  exact ⟨d,rfl,hrs.trans hd⟩

theorem ginzburgArrowPath_mem_generatorFiltration (a : Q.GinzburgArrow) (r : ℤ)
    (hr : r≤a.cohomologicalDegree Q) :
    Q.ginzburgArrowPath a ∈ Q.ginzburgGeneratorFiltrationPaths (a.source Q) (a.target Q) r :=
  ⟨⟨⟨a,rfl⟩,GinzburgPath.nil (a.source Q)⟩,rfl,hr⟩

universe u
variable (k : Type u) [Field k]

theorem ginzburgGeneratorFiltration_antitone (u v : Q.Vertex) {r s : ℤ} (hrs : r≤s) :
    Q.ginzburgGeneratorFiltration k u v s ≤ Q.ginzburgGeneratorFiltration k u v r :=
  Finsupp.supported_mono (Q.ginzburgGeneratorFiltrationPaths_antitone hrs)

theorem ginzburgGeneratorDifferential_mem_generatorFiltration (φ : Q.Potential k)
    (a : Q.GinzburgArrow) : Q.ginzburgGeneratorDifferential k φ a ∈
      Q.ginzburgGeneratorFiltration k (a.source Q) (a.target Q) (a.cohomologicalDegree Q+1) := by
  have ha : Finsupp.single (Q.ginzburgArrowPath a) (1:k) ∈
      Q.ginzburgAugmentationSubmodule k (a.source Q) (a.target Q) := by
    apply Finsupp.single_mem_supported
    simp [ginzburgArrowPath,GinzburgPath.length]
  have hd := Q.ginzburgDifferential_mem_augmentation k φ ha
  rw [Q.ginzburgDifferential_generator] at hd
  have hc := Q.ginzburgGeneratorDifferential_degree k φ a
  have hi : Q.ginzburgGeneratorDifferential k φ a ∈
      Q.ginzburgCohomologicalComponent k _ _ (a.cohomologicalDegree Q+1) ⊓
        Q.ginzburgAugmentationSubmodule k _ _ := ⟨hc,hd⟩
  change Q.ginzburgGeneratorDifferential k φ a ∈ Finsupp.supported k k _ ⊓
    Finsupp.supported k k _ at hi
  rw [←Finsupp.supported_inter] at hi
  apply Finsupp.supported_mono _ hi
  intro p hp
  apply Q.ginzburgGeneratorFiltrationPaths_of_degree hp.2
    (a.cohomologicalDegree Q+1)
  exact le_of_eq hp.1.symm

theorem GinzburgPath.differential_mem_generatorFiltration (φ : Q.Potential k)
    {u v : Q.Vertex} {r : ℤ} {p : Q.GinzburgPath u v}
    (hp : p ∈ Q.ginzburgGeneratorFiltrationPaths u v r) :
    p.differential Q k φ ∈ Q.ginzburgGeneratorFiltration k u v r := by
  obtain ⟨⟨⟨a,ha⟩,s⟩,rfl,hr⟩ := hp
  cases ha
  change r ≤ a.cohomologicalDegree Q at hr
  change (GinzburgPath.snoc s a rfl).differential Q k φ ∈ _
  rw [GinzburgPath.differential]
  apply Submodule.add_mem
  · apply Q.ginzburgGeneratorFiltration_comp k _ (Finsupp.single s 1)
    exact Q.ginzburgGeneratorFiltration_antitone k _ _ (by omega)
      (Q.ginzburgGeneratorDifferential_mem_generatorFiltration k φ a)
  · apply Submodule.smul_mem
    apply Q.ginzburgGeneratorFiltration_comp k _ (s.differential Q k φ)
    exact Finsupp.single_mem_supported _ _ (Q.ginzburgArrowPath_mem_generatorFiltration a r hr)

theorem ginzburgDifferential_mem_generatorFiltration (φ : Q.Potential k)
    {u v : Q.Vertex} {r : ℤ} {f : Q.GinzburgPathComponent k u v}
    (hf : f ∈ Q.ginzburgGeneratorFiltration k u v r) :
    Q.ginzburgDifferential k φ u v f ∈ Q.ginzburgGeneratorFiltration k u v r := by
  change f ∈ Finsupp.supported k k _ at hf
  rw [Finsupp.supported_eq_span_single] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p,hp,rfl⟩ := hx
    simp only [Q.ginzburgDifferential_single,one_smul]
    exact p.differential_mem_generatorFiltration Q k φ hp
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih => simpa only [map_smul] using Submodule.smul_mem _ a ih

end ASGinzburg.CutQuiver
