import ASGinzburg.GinzburgDifferentialGradings

/-! The differential vanishes on degree zero, including all original
paths. In particular the squares on original and dual generators vanish. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgCohomologicalComponent_eq_bot_of_pos (u v : Q.Vertex) {q : ℤ} (hq : 0<q) :
    Q.ginzburgCohomologicalComponent k u v q=⊥ := by
  change Finsupp.supported k k _=⊥
  have hs : {p : Q.GinzburgPath u v | p.cohomologicalDegree=q}=∅ := by
    ext p
    simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]
    intro hp
    have := p.cohomologicalDegree_nonpos
    omega
  rw [hs,Finsupp.supported_empty]

theorem ginzburgDifferential_degreeZero (φ : Q.Potential k) {u v : Q.Vertex}
    {f : Q.GinzburgPathComponent k u v} (hf : f ∈ Q.ginzburgCohomologicalComponent k u v 0) :
    Q.ginzburgDifferential k φ u v f=0 := by
  have hd := Q.ginzburgDifferential_degree k φ 0 hf
  rw [Q.ginzburgCohomologicalComponent_eq_bot_of_pos k u v (by norm_num)] at hd
  exact hd

theorem ginzburgDifferential_original (φ : Q.Potential k) {u v : Q.Vertex}
    (f : Q.PathComponent k u v) :
    Q.ginzburgDifferential k φ u v (Q.originalGinzburgLinearMap k u v f)=0 := by
  apply Q.ginzburgDifferential_degreeZero k φ
  rw [←Q.originalGinzburgLinearMap_range k]
  exact LinearMap.mem_range_self _ _

theorem ginzburgGeneratorDifferential_original_square (φ : Q.Potential k) (a : Q.Arrow) :
    Q.ginzburgDifferential k φ (Q.source a) (Q.target a)
      (Q.ginzburgGeneratorDifferential k φ (.original a))=0 := by
  exact map_zero _

theorem ginzburgGeneratorDifferential_dual_square (φ : Q.Potential k) (a : Q.Arrow) :
    Q.ginzburgDifferential k φ (Q.target a) (Q.source a)
      (Q.ginzburgGeneratorDifferential k φ (.dual a))=0 :=
  Q.ginzburgDifferential_original k φ (Q.pathCyclicDerivative k a φ)

end ASGinzburg.CutQuiver
