import work.ASGinzburgDraft.GinzburgSubstitutedOccurrenceWords
import work.ASGinzburgDraft.GinzburgCotangentOccurrenceTransport

/-! Exact finite word identities for the actual cotangent generator
images and the genuine inverse ordinary path automorphism. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgOriginalAutomorphismComponent_word
    (E : Q.VertexCutPathAutomorphism k) (i j : Q.Vertex) (f : Q.PathComponent k i j) :
    Q.ginzburgPathWordMap k i j
      (Q.originalGinzburgLinearMap k i j
        (VertexCutPathAutomorphism.componentLinearEquiv Q k E i j f)) =
      wordSubstitutionBetween (Q.ginzburgOriginalAutomorphismWordReplacement k E)
        (Q.pathWordMap k i j f) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g ihf ihg => simp only [map_add,ihf,ihg]
  | single p c =>
    have hs : (Finsupp.single p c : Q.PathComponent k i j) = c • Finsupp.single p 1 := by simp
    rw [hs]
    simp only [map_smul,Q.ginzburgOriginalAutomorphismPath_word,
      Q.pathWordMap_single,wordSubstitutionBetween_single,one_smul]

theorem ginzburgOriginalAutomorphismWordReplacement_one :
    Q.ginzburgOriginalAutomorphismWordReplacement k 1 =
      fun a => Finsupp.single [.original a] 1 := by
  funext a
  unfold ginzburgOriginalAutomorphismWordReplacement VertexCutPathAutomorphism.arrowReplacement
  rw [VertexCutPathAutomorphism.componentLinearEquiv_one]
  simp [pathIdentityArrowReplacement,Q.ginzburgPathWordMap_single,
    Path.originalGinzburg_toList,Path.toList]

theorem ginzburgOriginalAutomorphismWordReplacement_inverse
    (E : Q.VertexCutPathAutomorphism k) (b : Q.Arrow) :
    wordSubstitutionBetween (Q.ginzburgOriginalAutomorphismWordReplacement k E)
      (VertexCutPathAutomorphism.wordArrowReplacement Q k (E⁻¹) b) =
      Finsupp.single [.original b] 1 := by
  have h := Q.ginzburgOriginalAutomorphismComponent_word k E (Q.source b) (Q.target b)
    (VertexCutPathAutomorphism.arrowReplacement Q k (E⁻¹) b)
  rw [VertexCutPathAutomorphism.arrowReplacement,
    VertexCutPathAutomorphism.componentLinearEquiv_inv,
    LinearEquiv.apply_symm_apply] at h
  simpa [VertexCutPathAutomorphism.wordArrowReplacement,pathIdentityArrowReplacement,
    Q.ginzburgPathWordMap_single,Path.originalGinzburg_toList,Path.toList] using h.symm

theorem ginzburgPathWordMap_cotangentDualImage
    (E : Q.VertexCutPathAutomorphism k) (a : Q.Arrow) :
    Q.ginzburgPathWordMap k (Q.target a) (Q.source a) (Q.ginzburgCotangentDualImage k E a) =
      ∑ b : Q.Arrow,
        wordSubstitutedOccurrenceContext (Q.ginzburgOriginalAutomorphismWordReplacement k E) a
          (VertexCutPathAutomorphism.wordArrowReplacement Q k (E⁻¹) b)
          (Finsupp.single [.dual b] 1) := by
  classical
  rw [ginzburgCotangentDualImage,map_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [Q.ginzburgPathWordMap_substitutedOccurrenceDerivative]
  simp [VertexCutPathAutomorphism.wordArrowReplacement,Q.ginzburgPathWordMap_single,
    dualGinzburgArrowPath,GinzburgPath.toList]

end ASGinzburg.CutQuiver
