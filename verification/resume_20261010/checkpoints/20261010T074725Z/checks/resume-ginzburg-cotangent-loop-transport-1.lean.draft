import work.ASGinzburgDraft.GinzburgLoopTotalWords
import work.ASGinzburgDraft.GinzburgCotangentWordIdentities
import work.ASGinzburgDraft.WordSubstitutedOccurrenceCommutators
import work.ASGinzburgDraft.GinzburgVertexWordLocalization
import work.ASGinzburgDraft.GinzburgArrowSubstitutionGrading

/-! The genuine inverse-occurrence cotangent substitution fixes the
literal loop differential. Telescoping is localized by actual path sources. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgCotangentLoopDifferential_total_word
    (E : Q.VertexCutPathAutomorphism k) :
    (∑ v : Q.Vertex, Q.ginzburgPathWordMap k v v
      (Q.ginzburgArrowSubstitutionComponent k (Q.ginzburgCotangentArrowReplacement k E)
        v v (Q.ginzburgLoopDifferential k v))) =
      ∑ v : Q.Vertex, Q.ginzburgPathWordMap k v v (Q.ginzburgLoopDifferential k v) := by
  classical
  rw [Q.ginzburgLoopDifferential_total_substitution_word,
    Q.ginzburgLoopDifferential_total_word]
  change (∑ a : Q.Arrow,
    (wordConcatenation (Q.ginzburgOriginalAutomorphismWordReplacement k E a)
      (Q.ginzburgPathWordMap k (Q.target a) (Q.source a) (Q.ginzburgCotangentDualImage k E a)) -
    wordConcatenation
      (Q.ginzburgPathWordMap k (Q.target a) (Q.source a) (Q.ginzburgCotangentDualImage k E a))
      (Q.ginzburgOriginalAutomorphismWordReplacement k E a))) = _
  simp_rw [Q.ginzburgPathWordMap_cotangentDualImage k E]
  simp only [map_sum, LinearMap.sum_apply, ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [wordSubstitutedOccurrenceContext_commutator,
    Q.ginzburgOriginalAutomorphismWordReplacement_inverse k E b]

theorem ginzburgCotangentLoopDifferential_transport
    (E : Q.VertexCutPathAutomorphism k) (v : Q.Vertex) :
    Q.ginzburgArrowSubstitutionComponent k (Q.ginzburgCotangentArrowReplacement k E)
      v v (Q.ginzburgLoopDifferential k v) = Q.ginzburgLoopDifferential k v := by
  classical
  apply Q.ginzburgPathWordMap_injective k v v
  have h := congrArg (Q.ginzburgVertexWordProjection k v)
    (Q.ginzburgCotangentLoopDifferential_total_word k E)
  have hdegree (i : Q.Vertex) :
      Q.ginzburgArrowSubstitutionComponent k (Q.ginzburgCotangentArrowReplacement k E)
        i i (Q.ginzburgLoopDifferential k i) ∈ Q.ginzburgCohomologicalComponent k i i (-1) :=
    Q.ginzburgArrowSubstitutionComponent_mem_cohomological k
      (Q.ginzburgCotangentArrowReplacement k E)
      (Q.ginzburgCotangentArrowReplacement_mem_cohomological k E) i i (-1)
      (Q.ginzburgLoopDifferential k i) (Q.ginzburgLoopDifferential_degree k i)
  rw [Q.ginzburgVertexWordProjection_sum_pathWordMap_of_cohomological k v (-1) (by decide)
      (fun i => Q.ginzburgArrowSubstitutionComponent k (Q.ginzburgCotangentArrowReplacement k E)
        i i (Q.ginzburgLoopDifferential k i)) hdegree,
    Q.ginzburgVertexWordProjection_sum_pathWordMap_of_cohomological k v (-1) (by decide)
      (Q.ginzburgLoopDifferential k) (Q.ginzburgLoopDifferential_degree k)] at h
  exact h

end ASGinzburg.CutQuiver
