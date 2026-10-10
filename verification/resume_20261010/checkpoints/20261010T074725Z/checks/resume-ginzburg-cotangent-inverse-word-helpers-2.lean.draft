import work.ASGinzburgDraft.GinzburgCotangentWordIdentities
import work.ASGinzburgDraft.WordSubstitutedOccurrenceContextsComposition

/-! Literal original embedding and inverse ordinary substitutions provide
the actual finite identities used by the cotangent inverse. -/
namespace ASGinzburg
universe u v w
variable {A : Type u} {B : Type v} {k : Type w} [Field k] [DecidableEq A]

theorem wordSubstitutedOccurrenceContext_generator
    (σ : A → WordPolynomial k B) (a b : A) (h : WordPolynomial k B) :
    wordSubstitutedOccurrenceContext σ a (Finsupp.single [b] 1) h =
      if a = b then h else 0 := by
  by_cases hab : a = b <;>
    simp [hab,wordSubstitutedOccurrenceContextWord,wordSubstitutedOccurrenceContextAux,
      wordSubstitutedOccurrenceSandwich_apply,wordSubstitutionBetweenWord]

end ASGinzburg

namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgOriginalAutomorphismWordReplacement_from_ordinary
    (E : Q.VertexCutPathAutomorphism k) (b : Q.Arrow) :
    wordSubstitutionBetween (Q.ginzburgOriginalAutomorphismWordReplacement k 1)
      (VertexCutPathAutomorphism.wordArrowReplacement Q k E b) =
      Q.ginzburgOriginalAutomorphismWordReplacement k E b := by
  have h := Q.ginzburgOriginalAutomorphismComponent_word k 1 (Q.source b) (Q.target b)
    (VertexCutPathAutomorphism.arrowReplacement Q k E b)
  rw [VertexCutPathAutomorphism.componentLinearEquiv_one] at h
  exact h.symm

theorem VertexCutPathAutomorphism.wordArrowReplacement_substitute_inverse
    (E : Q.VertexCutPathAutomorphism k) (b : Q.Arrow) :
    wordSubstitutionBetween (VertexCutPathAutomorphism.wordArrowReplacement Q k E)
      (VertexCutPathAutomorphism.wordArrowReplacement Q k (E⁻¹) b) =
      Finsupp.single [b] 1 := by
  rw [wordSubstitutionBetween_same]
  have h := VertexCutPathAutomorphism.wordMap_component Q k E (Q.source b) (Q.target b)
    (VertexCutPathAutomorphism.arrowReplacement Q k (E⁻¹) b)
  rw [VertexCutPathAutomorphism.arrowReplacement,
    VertexCutPathAutomorphism.componentLinearEquiv_inv,
    LinearEquiv.apply_symm_apply] at h
  simpa [VertexCutPathAutomorphism.wordArrowReplacement,pathIdentityArrowReplacement,
    Path.toList] using h.symm

theorem ginzburgCotangentInverseWordComposition
    (E : Q.VertexCutPathAutomorphism k) (a c : Q.Arrow) (h : WordPolynomial k Q.GinzburgArrow) :
    (∑ b : Q.Arrow,
      wordSubstitutedOccurrenceContext (Q.ginzburgOriginalAutomorphismWordReplacement k 1) a
        (VertexCutPathAutomorphism.wordArrowReplacement Q k E b)
        (wordSubstitutedOccurrenceContext (Q.ginzburgOriginalAutomorphismWordReplacement k E) b
          (VertexCutPathAutomorphism.wordArrowReplacement Q k (E⁻¹) c) h)) =
      if a = c then h else 0 := by
  have hc := wordSubstitutedOccurrenceContext_composition
    (VertexCutPathAutomorphism.wordArrowReplacement Q k E)
    (Q.ginzburgOriginalAutomorphismWordReplacement k 1) a
    (VertexCutPathAutomorphism.wordArrowReplacement Q k (E⁻¹) c) h
  have hm : (fun b => wordSubstitutionBetween (Q.ginzburgOriginalAutomorphismWordReplacement k 1)
      (VertexCutPathAutomorphism.wordArrowReplacement Q k E b)) =
      Q.ginzburgOriginalAutomorphismWordReplacement k E := by
    funext b
    exact Q.ginzburgOriginalAutomorphismWordReplacement_from_ordinary k E b
  rw [hm,VertexCutPathAutomorphism.wordArrowReplacement_substitute_inverse,
    wordSubstitutedOccurrenceContext_generator] at hc
  exact hc.symm

end ASGinzburg.CutQuiver
