import ASGinzburg.GinzburgGeneratorLayerQuotients

/-! Each actual generator layer has the genuine shifted prefix basis,
with the original, dual or loop generators of that degree. -/
namespace ASGinzburg.CutQuiver
variable (Q : CutQuiver)

theorem GinzburgLastGeneratorData.path_mem_layer_iff {u v : Q.Vertex}
    (d : Q.GinzburgLastGeneratorData u v) (r : ℤ) :
    d.path Q ∈ Q.ginzburgGeneratorLayerPaths u v r ↔ d.1.val.cohomologicalDegree Q=r := by
  constructor
  · rintro ⟨e,he,hd⟩
    have heq := GinzburgLastGeneratorData.path_injective Q u v he
    subst e
    exact hd
  · intro hd
    exact ⟨d,rfl,hd⟩

def ginzburgGeneratorLayerDegreeEquiv (u v : Q.Vertex) (r q c : ℤ) :
    {p : Q.GinzburgPath u v // p ∈ Q.ginzburgGeneratorLayerPaths u v r ∧
      p.cohomologicalDegree=q ∧ p.cutDegree=c} ≃
    Σ a : {a : Q.GinzburgArrow // a.target Q=v ∧ a.cohomologicalDegree Q=r},
      {p : Q.GinzburgPath u (a.val.source Q) //
        p.cohomologicalDegree=q-r ∧ p.cutDegree=c-a.val.cutDegree Q} where
  toFun p := by
    have hp := Q.ginzburgGeneratorFiltrationPaths_nonempty
      (Q.ginzburgGeneratorLayerPaths_le_filtration u v r p.property.1)
    let d := p.val.lastGenerator Q hp
    have hd : d.1.val.cohomologicalDegree Q=r := by
      apply (d.path_mem_layer_iff Q r).mp
      rw [p.val.lastGenerator_path]
      exact p.property.1
    refine ⟨⟨d.1.val,⟨d.1.property,hd⟩⟩,⟨d.2,?_,?_⟩⟩
    · have he := d.path_cohomologicalDegree Q
      rw [p.val.lastGenerator_path,hd] at he
      have hq := p.property.2.1
      omega
    · apply (d.path_cutDegree_iff Q c).mp
      rw [p.val.lastGenerator_path]
      exact p.property.2.2
  invFun a := by
    let d : Q.GinzburgLastGeneratorData u v := ⟨⟨a.1.val,a.1.property.1⟩,a.2.val⟩
    refine ⟨d.path Q,⟨d,rfl,a.1.property.2⟩,?_,?_⟩
    · rw [d.path_cohomologicalDegree]
      have hq := a.2.property.1
      have hr := a.1.property.2
      change a.2.val.cohomologicalDegree+a.1.val.cohomologicalDegree Q=q
      omega
    · apply (d.path_cutDegree_iff Q c).mpr
      exact a.2.property.2
  left_inv p := by
    apply Subtype.ext
    exact p.val.lastGenerator_path Q _
  right_inv a := by
    obtain ⟨⟨a,ha⟩,p⟩ := a
    obtain ⟨ht,hr⟩ := ha
    cases ht
    rfl

universe u
variable (k : Type u) [Field k]

noncomputable def ginzburgGeneratorLayerFreeEquiv (u v : Q.Vertex) (r q c : ℤ) :
    Q.ginzburgGeneratorLayerAtDegree k u v r q c ≃ₗ[k]
      (Π a : {a : Q.GinzburgArrow // a.target Q=v ∧ a.cohomologicalDegree Q=r},
        Q.ginzburgCutCohomologicalComponent k u (a.val.source Q)
          (q-r) (c-a.val.cutDegree Q)) := by
  classical
  letI := Fintype.ofFinite {a : Q.GinzburgArrow // a.target Q=v ∧ a.cohomologicalDegree Q=r}
  exact (Finsupp.supportedEquivFinsupp (M:=k) (R:=k) _).trans
    ((Finsupp.domLCongr (Q.ginzburgGeneratorLayerDegreeEquiv u v r q c)).trans
      ((Finsupp.sigmaFinsuppLEquivPiFinsupp k).trans
        (LinearEquiv.piCongrRight fun a =>
          (Q.ginzburgCutComponentBasisEquiv k u (a.val.source Q)
            (q-r) (c-a.val.cutDegree Q)).symm)))

end ASGinzburg.CutQuiver
