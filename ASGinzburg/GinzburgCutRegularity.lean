import ASGinzburg.GinzburgCutRetracts
import ASGinzburg.GinzburgCycleBoundary
import ASGinzburg.GinzburgCutDecomposition

/-! Actual Ginzburg regularity is equivalent to vanishing of negative
homology in every actual fixed-cut complex. The converse uses finite
support decomposition of cycles and actual boundary preimages. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgHomology_succ_isZero_of_cut (φ : Q.Potential k)
    (u v : Q.Vertex) (q : ℤ)
    (h : ∀ c : ℤ, IsZero (Q.ginzburgCutHomology k φ u v c (q+1))) :
    IsZero (Q.ginzburgHomology k φ u v (q+1)) := by
  apply (Q.ginzburgHomology_succ_isZero_iff_cycles k φ u v q).mpr
  intro f hf
  have hex (c : ℤ) : ∃ g : Q.ginzburgCutCohomologicalComponent k u v q c,
      Q.ginzburgDifferential k φ u v g.val=Q.ginzburgCutProjection k u v c f.val := by
    apply (Q.ginzburgCutHomology_succ_isZero_iff_cycles k φ u v c q).mp (h c)
      ⟨Q.ginzburgCutProjection k u v c f.val,
        Q.ginzburgCutProjection_cohomological k c (q+1) f.property,
        Q.ginzburgCutProjection_mem k c f.val⟩
    change Q.ginzburgDifferential k φ u v (Q.ginzburgCutProjection k u v c f.val)=0
    rw [Q.ginzburgDifferential_cutProjection,hf,map_zero]
  choose g hg using hex
  let g' (c : ℤ) : Q.ginzburgCohomologicalComponent k u v q := ⟨(g c).val,(g c).property.1⟩
  refine ⟨∑ c ∈ Q.ginzburgCutSupport k f.val, g' c,?_⟩
  change Q.ginzburgDifferential k φ u v
    ((∑ c ∈ Q.ginzburgCutSupport k f.val, g' c).val)=f.val
  simp only [Submodule.coe_sum,map_sum]
  change (∑ c ∈ Q.ginzburgCutSupport k f.val,
    Q.ginzburgDifferential k φ u v (g c).val)=f.val
  simp_rw [hg]
  exact Q.ginzburgCutProjection_sum k f.val

theorem ginzburgRegular_iff_cutHomology (φ : Q.Potential k) :
    Q.GinzburgRegular k φ ↔ ∀ u v : Q.Vertex, ∀ c q : ℤ, q<0 →
      IsZero (Q.ginzburgCutHomology k φ u v c q) := by
  constructor
  · intro h u v c q hq
    exact h.cutHomology_isZero Q k u v c q hq
  · intro h
    apply (Q.ginzburgRegular_iff_components k φ).mpr
    intro u v q hq
    obtain ⟨r,rfl⟩ : ∃ r : ℤ, q=r+1 := ⟨q-1,by omega⟩
    exact Q.ginzburgHomology_succ_isZero_of_cut k φ u v r (fun c => h u v c (r+1) hq)

end ASGinzburg.CutQuiver
