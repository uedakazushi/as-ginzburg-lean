import work.ASGinzburgDraft.GinzburgCotangentInverseWordHelpers
import work.ASGinzburgDraft.GinzburgArrowSubstitutionInverse

/-! Actual inverse occurrence identities give literal inverse extended
generator substitutions. No inverse compatibility is assumed. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgCotangentSubstitution_dual_inverse
    (E : Q.VertexCutPathAutomorphism k) (a : Q.Arrow) :
    Q.ginzburgArrowSubstitutionComponent k (Q.ginzburgCotangentArrowReplacement k E)
      (Q.target a) (Q.source a) (Q.ginzburgCotangentDualImage k (E⁻¹) a) =
      Finsupp.single (Q.dualGinzburgArrowPath a) 1 := by
  classical
  have hd (b : Q.Arrow) :
      Q.ginzburgArrowSubstitutionComponent k (Q.ginzburgCotangentArrowReplacement k E)
        (Q.target b) (Q.source b) (Finsupp.single (Q.dualGinzburgArrowPath b) 1) =
        Q.ginzburgCotangentDualImage k E b :=
    Q.ginzburgArrowSubstitutionComponent_arrow k _ (.dual b)
  have hs : Q.ginzburgArrowSubstitutionComponent k (Q.ginzburgCotangentArrowReplacement k E)
      (Q.target a) (Q.source a) (Q.ginzburgCotangentDualImage k (E⁻¹) a) =
      ∑ b : Q.Arrow,
        Q.ginzburgSubstitutedOccurrenceDerivative k 1 a (Q.source b) (Q.target b)
          (VertexCutPathAutomorphism.arrowReplacement Q k E b)
          (Q.ginzburgCotangentDualImage k E b) := by
    rw [ginzburgCotangentDualImage,map_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [Q.ginzburgCotangentSubstitution_occurrenceDerivative,mul_inv_cancel,inv_inv,hd]
  rw [hs]
  apply Q.ginzburgPathWordMap_injective k
  rw [map_sum,Q.ginzburgPathWordMap_single]
  simp_rw [Q.ginzburgPathWordMap_substitutedOccurrenceDerivative,
    Q.ginzburgPathWordMap_cotangentDualImage]
  change (∑ b : Q.Arrow,
    wordSubstitutedOccurrenceContext (Q.ginzburgOriginalAutomorphismWordReplacement k 1) a
      (VertexCutPathAutomorphism.wordArrowReplacement Q k E b)
      (∑ c : Q.Arrow,
        wordSubstitutedOccurrenceContext (Q.ginzburgOriginalAutomorphismWordReplacement k E) b
          (VertexCutPathAutomorphism.wordArrowReplacement Q k (E⁻¹) c)
          (Finsupp.single [.dual c] 1))) = _
  simp only [map_sum]
  rw [Finset.sum_comm]
  simp_rw [Q.ginzburgCotangentInverseWordComposition]
  simp [dualGinzburgArrowPath,GinzburgPath.toList]

theorem ginzburgCotangentArrowReplacement_inverse
    (E : Q.VertexCutPathAutomorphism k) (a : Q.GinzburgArrow) :
    Q.ginzburgArrowSubstitutionComponent k (Q.ginzburgCotangentArrowReplacement k E)
      (a.source Q) (a.target Q) (Q.ginzburgCotangentArrowReplacement k (E⁻¹) a) =
      Q.ginzburgIdentityArrowReplacement k a := by
  cases a with
  | original a =>
    change Q.ginzburgArrowSubstitutionComponent k (Q.ginzburgCotangentArrowReplacement k E)
      (Q.source a) (Q.target a) (Q.originalGinzburgLinearMap k _ _
        (VertexCutPathAutomorphism.arrowReplacement Q k (E⁻¹) a)) = _
    rw [Q.ginzburgCotangentSubstitution_original,VertexCutPathAutomorphism.arrowReplacement,
      VertexCutPathAutomorphism.componentLinearEquiv_inv,LinearEquiv.apply_symm_apply]
    simp [pathIdentityArrowReplacement,ginzburgIdentityArrowReplacement,
      ginzburgArrowPath,Path.originalGinzburg,GinzburgArrow.source]
  | dual a => exact Q.ginzburgCotangentSubstitution_dual_inverse k E a
  | loop v => exact Q.ginzburgArrowSubstitutionComponent_arrow k _ (.loop v)

theorem ginzburgCotangentArrowReplacement_inverse_reverse
    (E : Q.VertexCutPathAutomorphism k) (a : Q.GinzburgArrow) :
    Q.ginzburgArrowSubstitutionComponent k (Q.ginzburgCotangentArrowReplacement k (E⁻¹))
      (a.source Q) (a.target Q) (Q.ginzburgCotangentArrowReplacement k E a) =
      Q.ginzburgIdentityArrowReplacement k a := by
  simpa only [inv_inv] using Q.ginzburgCotangentArrowReplacement_inverse k (E⁻¹) a

end ASGinzburg.CutQuiver
