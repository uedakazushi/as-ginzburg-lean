import ASGinzburg.GinzburgBoundaryLengthSupport
import ASGinzburg.GinzburgGeneratorLayerCoefficients

/-! Removing the last generator lowers genuine path length by exactly
one, so coefficients of length-two boundaries have nonempty prefixes. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgGeneratorLayerFreeEquiv_supported_length
    (u v : Q.Vertex) (r q c : ℤ) (n : ℕ)
    (f : Q.ginzburgGeneratorLayerAtDegree k u v r q c)
    (hf : f.val ∈ Finsupp.supported k k
      {p : Q.GinzburgPath u v | n+1 ≤ p.length})
    (a : {a : Q.GinzburgArrow // a.target Q=v ∧ a.cohomologicalDegree Q=r}) :
    (Q.ginzburgGeneratorLayerFreeEquiv k u v r q c f a).val ∈
      Finsupp.supported k k {p : Q.GinzburgPath u (a.val.source Q) | n ≤ p.length} := by
  apply (Finsupp.mem_supported' k _).mpr
  intro p hp
  by_cases hq : p.cohomologicalDegree=q-r ∧ p.cutDegree=c-a.val.cutDegree Q
  · rw [Q.ginzburgGeneratorLayerFreeEquiv_apply k u v r q c f a ⟨p,hq⟩]
    apply (Finsupp.mem_supported' k _).mp hf
    change ¬ n+1 ≤ (GinzburgLastGeneratorData.path Q ⟨⟨a.val,a.property.1⟩,p⟩).length
    rw [GinzburgLastGeneratorData.path_length]
    change ¬ n+1 ≤ p.length+1
    change ¬ n ≤ p.length at hp
    omega
  · let z := Q.ginzburgGeneratorLayerFreeEquiv k u v r q c f a
    by_cases hd : p.cohomologicalDegree=q-r
    · have hc : p.cutDegree≠c-a.val.cutDegree Q := fun hc => hq ⟨hd,hc⟩
      exact (Finsupp.mem_supported' k z.val).mp z.property.2 p hc
    · exact (Finsupp.mem_supported' k z.val).mp z.property.1 p hd

end ASGinzburg.CutQuiver
