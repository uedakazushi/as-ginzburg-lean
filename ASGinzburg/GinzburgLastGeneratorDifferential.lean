import ASGinzburg.GinzburgGeneratorLayerBasis

/-! Modulo the next actual generator layer, differentiating a path
ending in a generator is exactly the signed differential of its prefix. -/
namespace ASGinzburg.CutQuiver
variable (Q : CutQuiver)

theorem ginzburgGeneratorLayerPaths_comp {u v w : Q.Vertex}
    (p : Q.GinzburgPath u v) {q : Q.GinzburgPath v w} {r : ℤ}
    (hq : q ∈ Q.ginzburgGeneratorLayerPaths v w r) :
    p.comp q ∈ Q.ginzburgGeneratorLayerPaths u w r := by
  obtain ⟨⟨⟨a,ha⟩,s⟩,rfl,hr⟩ := hq
  cases ha
  exact ⟨⟨⟨a,rfl⟩,p.comp s⟩,rfl,hr⟩

universe u
variable (k : Type u) [Field k]

theorem ginzburgGeneratorLayer_comp {u v w : Q.Vertex} {r : ℤ}
    {g : Q.GinzburgPathComponent k v w} (hg : g ∈ Q.ginzburgGeneratorLayer k v w r)
    (f : Q.GinzburgPathComponent k u v) :
    Q.ginzburgPathComp k g f ∈ Q.ginzburgGeneratorLayer k u w r := by
  apply Q.ginzburgSupported_comp k Set.univ (Q.ginzburgGeneratorLayerPaths v w r)
    (Q.ginzburgGeneratorLayerPaths u w r) _
      (by rw [Finsupp.supported_univ]; trivial) hg
  intro p _hp q hq
  exact Q.ginzburgGeneratorLayerPaths_comp p hq

theorem ginzburgAppendGenerator_mem_layer (a : Q.GinzburgArrow) {u : Q.Vertex}
    (f : Q.GinzburgPathComponent k u (a.source Q)) :
    Q.ginzburgPathComp k (Finsupp.single (Q.ginzburgArrowPath a) 1) f ∈
      Q.ginzburgGeneratorLayer k u (a.target Q) (a.cohomologicalDegree Q) := by
  apply Q.ginzburgGeneratorLayer_comp k _ f
  exact Finsupp.single_mem_supported _ _
    ⟨⟨⟨a,rfl⟩,GinzburgPath.nil (a.source Q)⟩,rfl,rfl⟩

theorem ginzburgDifferential_appendGenerator_mod_filtration (φ : Q.Potential k)
    (a : Q.GinzburgArrow) {u : Q.Vertex}
    (f : Q.GinzburgPathComponent k u (a.source Q)) :
    Q.ginzburgDifferential k φ u (a.target Q)
      (Q.ginzburgPathComp k (Finsupp.single (Q.ginzburgArrowPath a) 1) f)-
        ginzburgSign k (a.cohomologicalDegree Q) •
          Q.ginzburgPathComp k (Finsupp.single (Q.ginzburgArrowPath a) 1)
            (Q.ginzburgDifferential k φ u (a.source Q) f) ∈
      Q.ginzburgGeneratorFiltration k u (a.target Q) (a.cohomologicalDegree Q+1) := by
  have ha : Finsupp.single (Q.ginzburgArrowPath a) (1:k) ∈
      Q.ginzburgCohomologicalComponent k (a.source Q) (a.target Q)
        (a.cohomologicalDegree Q) := by
    apply Finsupp.single_mem_supported
    simp [ginzburgArrowPath,GinzburgPath.cohomologicalDegree]
  rw [Q.ginzburgDifferential_comp_homogeneous k φ f _ _ ha,
    Q.ginzburgDifferential_generator,add_sub_cancel_right]
  exact Q.ginzburgGeneratorFiltration_comp k
    (Q.ginzburgGeneratorDifferential_mem_generatorFiltration k φ a) f

end ASGinzburg.CutQuiver
