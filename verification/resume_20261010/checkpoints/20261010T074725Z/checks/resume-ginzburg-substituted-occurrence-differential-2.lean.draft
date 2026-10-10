import work.ASGinzburgDraft.GinzburgSubstitutedOccurrenceContexts

/-! Arbitrary inserted extended polynomials retain their genuine degree,
and actual occurrence insertion commutes with the Ginzburg differential. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgSubstitutedOccurrenceOperator_mem_cohomological
    (E : Q.VertexCutPathAutomorphism k) (a : Q.Arrow)
    {i j : Q.Vertex} (p : Q.Path i j) {q : ℤ}
    (h : Q.GinzburgPathComponent k j i)
    (hh : h ∈ Q.ginzburgCohomologicalComponent k j i q) :
    Q.ginzburgSubstitutedOccurrenceOperator k E a p h ∈
      Q.ginzburgCohomologicalComponent k (Q.target a) (Q.source a) q := by
  have hL : ∀ L : List (Q.PathOccurrenceContext a i j),
      (L.map (Q.ginzburgSubstitutedOccurrenceContextMap k E)).sum h ∈
        Q.ginzburgCohomologicalComponent k (Q.target a) (Q.source a) q := by
    intro L
    induction L with
    | nil => simp
    | cons C L ih =>
      simpa only [List.map_cons,List.sum_cons,LinearMap.add_apply] using
        (Q.ginzburgCohomologicalComponent k _ _ q).add_mem
          (Q.ginzburgSubstitutedOccurrenceContextMap_mem_cohomological k E C h hh) ih
  exact hL (p.occurrenceContexts Q a)

theorem ginzburgSubstitutedOccurrenceDerivative_mem_cohomological
    (E : Q.VertexCutPathAutomorphism k) (a : Q.Arrow) (i j : Q.Vertex)
    (f : Q.PathComponent k i j) {q : ℤ}
    (h : Q.GinzburgPathComponent k j i)
    (hh : h ∈ Q.ginzburgCohomologicalComponent k j i q) :
    Q.ginzburgSubstitutedOccurrenceDerivative k E a i j f h ∈
      Q.ginzburgCohomologicalComponent k (Q.target a) (Q.source a) q := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g ihf ihg =>
    simpa only [map_add,LinearMap.add_apply] using
      (Q.ginzburgCohomologicalComponent k _ _ q).add_mem ihf ihg
  | single p c =>
    simpa only [Q.ginzburgSubstitutedOccurrenceDerivative_single,LinearMap.smul_apply] using
      (Q.ginzburgCohomologicalComponent k _ _ q).smul_mem c
        (Q.ginzburgSubstitutedOccurrenceOperator_mem_cohomological k E a p h hh)

theorem ginzburgSubstitutedOccurrenceOperator_differential
    (E : Q.VertexCutPathAutomorphism k) (φ : Q.Potential k) (a : Q.Arrow)
    {i j : Q.Vertex} (p : Q.Path i j) (h : Q.GinzburgPathComponent k j i) :
    Q.ginzburgDifferential k φ (Q.target a) (Q.source a)
      (Q.ginzburgSubstitutedOccurrenceOperator k E a p h) =
      Q.ginzburgSubstitutedOccurrenceOperator k E a p
        (Q.ginzburgDifferential k φ j i h) := by
  have hL : ∀ L : List (Q.PathOccurrenceContext a i j),
      Q.ginzburgDifferential k φ (Q.target a) (Q.source a)
        ((L.map (Q.ginzburgSubstitutedOccurrenceContextMap k E)).sum h) =
      (L.map (Q.ginzburgSubstitutedOccurrenceContextMap k E)).sum
        (Q.ginzburgDifferential k φ j i h) := by
    intro L
    induction L with
    | nil => simp
    | cons C L ih =>
      simp only [List.map_cons,List.sum_cons,LinearMap.add_apply,map_add,
        Q.ginzburgSubstitutedOccurrenceContextMap_differential,ih]
  exact hL (p.occurrenceContexts Q a)

theorem ginzburgSubstitutedOccurrenceDerivative_differential
    (E : Q.VertexCutPathAutomorphism k) (φ : Q.Potential k) (a : Q.Arrow)
    (i j : Q.Vertex) (f : Q.PathComponent k i j)
    (h : Q.GinzburgPathComponent k j i) :
    Q.ginzburgDifferential k φ (Q.target a) (Q.source a)
      (Q.ginzburgSubstitutedOccurrenceDerivative k E a i j f h) =
      Q.ginzburgSubstitutedOccurrenceDerivative k E a i j f
        (Q.ginzburgDifferential k φ j i h) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g ihf ihg => simp only [map_add,LinearMap.add_apply,ihf,ihg]
  | single p c =>
    simp only [Q.ginzburgSubstitutedOccurrenceDerivative_single,
      LinearMap.smul_apply,map_smul,
      Q.ginzburgSubstitutedOccurrenceOperator_differential]

end ASGinzburg.CutQuiver
