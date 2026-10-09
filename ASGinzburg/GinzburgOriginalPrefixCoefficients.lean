import ASGinzburg.GinzburgOriginalFilteredPrefixes
import ASGinzburg.GinzburgGeneratorLayerCoefficients

/-! The native upper filtered-to-prefix map reads the actual
last original generator coefficient of every representative. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgOriginalFilteredToPrefix_coefficient (φ : Q.Potential k)
    (u v : Q.Vertex) (c : ℤ)
    (z : Q.ginzburgGeneratorFiltrationAtDegree k u v 0 0 c)
    (a : {a : Q.GinzburgArrow // a.target Q=v ∧ a.cohomologicalDegree Q=0})
    (p : {p : Q.GinzburgPath u (a.val.source Q) //
      p.cohomologicalDegree=0-0 ∧ p.cutDegree=c-a.val.cutDegree Q}) :
    (((Q.ginzburgOriginalFilteredToPrefix k φ u v c).f 0 z) a).val p.val=
      z.val ((GinzburgLastGeneratorData.path Q) ⟨⟨a.val,a.property.1⟩,p.val⟩) := by
  classical
  let d : Q.GinzburgLastGeneratorData u v := ⟨⟨a.val,a.property.1⟩,p.val⟩
  have hd : d.path Q ∈ {p : Q.GinzburgPath u v |
      p ∈ Q.ginzburgGeneratorLayerPaths u v 0 ∧ p.cohomologicalDegree=0 ∧ p.cutDegree=c} := by
    refine ⟨(d.path_mem_layer_iff Q 0).mpr a.property.2,?_,?_⟩
    · rw [d.path_cohomologicalDegree Q]
      have hp := p.property.1
      have ha := a.property.2
      change p.val.cohomologicalDegree+a.val.cohomologicalDegree Q=0
      omega
    · exact (d.path_cutDegree_iff Q c).mpr p.property.2
  rw [Q.ginzburgOriginalFilteredToPrefix_f,
    Q.ginzburgGeneratorLayerFreeEquiv_apply k u v 0 0 c _ a p,
    Q.ginzburgGeneratorLayerQuotientEquiv_coe_mk]
  exact Finsupp.filter_apply_pos _ _ hd

end ASGinzburg.CutQuiver
