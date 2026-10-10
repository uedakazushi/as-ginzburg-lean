import work.ASGinzburgDraft.GinzburgCotangentArrowReplacement
import work.ASGinzburgDraft.GinzburgOriginalArrowSubstitution
import ASGinzburg.PathAutomorphismComponents

/-! Literal cotangent substitutions transport extended occurrence
contexts by the actual ordinary group composition. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgCotangentSubstitution_original
    (E : Q.VertexCutPathAutomorphism k) (i j : Q.Vertex)
    (f : Q.PathComponent k i j) :
    Q.ginzburgArrowSubstitutionComponent k (Q.ginzburgCotangentArrowReplacement k E) i j
      (Q.originalGinzburgLinearMap k i j f) =
      Q.originalGinzburgLinearMap k i j
        (VertexCutPathAutomorphism.componentLinearEquiv Q k E i j f) := by
  rw [VertexCutPathAutomorphism.component_substitution]
  exact Q.ginzburgArrowSubstitutionComponent_original k _ _ (fun _ => rfl) i j f

theorem ginzburgCotangentSubstitution_occurrenceContext
    (E F : Q.VertexCutPathAutomorphism k) {a : Q.Arrow} {i j : Q.Vertex}
    (C : Q.PathOccurrenceContext a i j) (h : Q.GinzburgPathComponent k j i) :
    Q.ginzburgArrowSubstitutionComponent k (Q.ginzburgCotangentArrowReplacement k E)
      (Q.target a) (Q.source a) (Q.ginzburgSubstitutedOccurrenceContextMap k F C h) =
      Q.ginzburgSubstitutedOccurrenceContextMap k (E*F) C
        (Q.ginzburgArrowSubstitutionComponent k (Q.ginzburgCotangentArrowReplacement k E) j i h) := by
  rw [Q.ginzburgSubstitutedOccurrenceContextMap_apply,
    Q.ginzburgArrowSubstitutionComponent_comp,Q.ginzburgArrowSubstitutionComponent_comp,
    Q.ginzburgCotangentSubstitution_original,Q.ginzburgCotangentSubstitution_original,
    ← VertexCutPathAutomorphism.componentLinearEquiv_mul_apply,
    ← VertexCutPathAutomorphism.componentLinearEquiv_mul_apply,
    Q.ginzburgSubstitutedOccurrenceContextMap_apply]

theorem ginzburgCotangentSubstitution_occurrenceOperator
    (E F : Q.VertexCutPathAutomorphism k) (a : Q.Arrow)
    {i j : Q.Vertex} (p : Q.Path i j) (h : Q.GinzburgPathComponent k j i) :
    Q.ginzburgArrowSubstitutionComponent k (Q.ginzburgCotangentArrowReplacement k E)
      (Q.target a) (Q.source a) (Q.ginzburgSubstitutedOccurrenceOperator k F a p h) =
      Q.ginzburgSubstitutedOccurrenceOperator k (E*F) a p
        (Q.ginzburgArrowSubstitutionComponent k (Q.ginzburgCotangentArrowReplacement k E) j i h) := by
  have hL : ∀ L : List (Q.PathOccurrenceContext a i j),
      Q.ginzburgArrowSubstitutionComponent k (Q.ginzburgCotangentArrowReplacement k E)
        (Q.target a) (Q.source a)
        ((L.map (Q.ginzburgSubstitutedOccurrenceContextMap k F)).sum h) =
      (L.map (Q.ginzburgSubstitutedOccurrenceContextMap k (E*F))).sum
        (Q.ginzburgArrowSubstitutionComponent k (Q.ginzburgCotangentArrowReplacement k E) j i h) := by
    intro L
    induction L with
    | nil => simp
    | cons C L ih =>
      simp only [List.map_cons,List.sum_cons,LinearMap.add_apply,map_add,
        Q.ginzburgCotangentSubstitution_occurrenceContext,ih]
  exact hL (p.occurrenceContexts Q a)

theorem ginzburgCotangentSubstitution_occurrenceDerivative
    (E F : Q.VertexCutPathAutomorphism k) (a : Q.Arrow) (i j : Q.Vertex)
    (f : Q.PathComponent k i j) (h : Q.GinzburgPathComponent k j i) :
    Q.ginzburgArrowSubstitutionComponent k (Q.ginzburgCotangentArrowReplacement k E)
      (Q.target a) (Q.source a) (Q.ginzburgSubstitutedOccurrenceDerivative k F a i j f h) =
      Q.ginzburgSubstitutedOccurrenceDerivative k (E*F) a i j f
        (Q.ginzburgArrowSubstitutionComponent k (Q.ginzburgCotangentArrowReplacement k E) j i h) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g ihf ihg => simp only [map_add,LinearMap.add_apply,ihf,ihg]
  | single p c =>
    simp only [Q.ginzburgSubstitutedOccurrenceDerivative_single,LinearMap.smul_apply,
      map_smul,Q.ginzburgCotangentSubstitution_occurrenceOperator]

end ASGinzburg.CutQuiver
