import work.ASGinzburgDraft.TriangleGinzburgGLSubstitutionInverse
import work.ASGinzburgDraft.TriangleGLCyclicDerivativeContragredient
import work.ASGinzburgDraft.GinzburgOriginalWordMap

/-! The actual inverse-transpose extension intertwines genuine dual
Ginzburg generator differentials, derived from the actual cyclic chain rule. -/
namespace ASGinzburg
universe u
variable (k : Type u) [Field k]

theorem triangleGinzburgDualCoordinates_differential_word
    (φ : triangle333.Potential k) (s : Fin 3) (x : ArrowSpace333 k) :
    triangle333.ginzburgPathWordMap k (triangleEdgeTarget s) s
      (triangle333.ginzburgDifferential k φ (triangleEdgeTarget s) s
        (triangleGinzburgDualCoordinates k s x)) =
      ∑ i : Fin 3, x i • triangle333.originalGinzburgWordMap k
        (cyclicDerivative (triangleEdgeArrow s i) φ.val) := by
  classical
  have hSingle : ∀ i : Fin 3,
      triangle333.ginzburgPathWordMap k (triangleEdgeTarget s) s
        (triangle333.ginzburgDifferential k φ (triangleEdgeTarget s) s
          (Finsupp.single (triangleEdgeDualGinzburgPath s i) 1)) =
      triangle333.originalGinzburgWordMap k
        (cyclicDerivative (triangleEdgeArrow s i) φ.val) := by
    intro i
    have h := triangle333.ginzburgPathWordMap_dualGeneratorDifferential k φ (triangleEdgeArrow s i)
    rw [←triangle333.ginzburgDifferential_generator] at h
    fin_cases s <;> fin_cases i <;>
      simpa [triangleEdgeDualGinzburgPath,triangleEdgeArrow,triangleEdgeTarget,triangle333,
        CutQuiver.GinzburgPath.transport,CutQuiver.dualGinzburgArrowPath,
        CutQuiver.ginzburgArrowPath,CutQuiver.GinzburgArrow.source,
        CutQuiver.GinzburgArrow.target] using h
  rw [triangleGinzburgDualCoordinates_apply]
  simp only [map_sum,map_smul,hSingle]

theorem triangleGinzburgGLDualArrow_differential (g : TriangleGL333 k)
    (φ : triangle333.Potential k) (b : triangle333.Arrow) :
    triangle333.ginzburgDifferential k
      (CutQuiver.VertexCutPathAutomorphism.potentialLinearEquiv triangle333 k
        (triangleGLPathAutomorphism k g) φ) (triangle333.target b) (triangle333.source b)
      (triangleGinzburgGLArrowReplacement k g (.dual b)) =
      triangle333.ginzburgArrowSubstitutionComponent k (triangleGinzburgGLArrowReplacement k g)
        (triangle333.target b) (triangle333.source b)
        (triangle333.ginzburgGeneratorDifferential k φ (.dual b)) := by
  apply triangle333.ginzburgPathWordMap_injective k
  change triangle333.ginzburgPathWordMap k _ _
      (triangle333.ginzburgDifferential k
        (CutQuiver.VertexCutPathAutomorphism.potentialLinearEquiv triangle333 k
          (triangleGLPathAutomorphism k g) φ) _ _
        (triangleGinzburgDualCoordinates k (triangle333.source b)
          (triangleArrowContragredient k (triangleGLArrowMatrix k g (triangle333.source b))
            (Pi.single (triangleGLArrowIndex b) 1)))) =
    triangle333.ginzburgPathWordMap k _ _
      (triangle333.ginzburgArrowSubstitutionComponent k (triangleGinzburgGLArrowReplacement k g)
        _ _ (triangle333.originalGinzburgLinearMap k _ _ (triangle333.pathCyclicDerivative k b φ)))
  rw [triangleGinzburgDualCoordinates_differential_word,triangleGinzburgGLSubstitution_original,
    triangle333.ginzburgPathWordMap_original,←triangleGLPathAutomorphism_component,
    CutQuiver.VertexCutPathAutomorphism.wordMap_component,
    triangle333.pathWordMap_pathCyclicDerivative]
  have he : CutQuiver.VertexCutPathAutomorphism.wordArrowReplacement triangle333 k
      (triangleGLPathAutomorphism k g) =
        wordLinearArrowReplacement (triangleGLWordArrowCoefficient k g) := by
    funext a
    exact triangleGLPathAutomorphism_wordArrowReplacement k g a
  rw [he]
  have h := congrArg (triangle333.originalGinzburgWordMap k)
    (triangleGL_wordDerivative_contragredient_block k g b φ).symm
  simp only [map_sum,map_smul] at h
  simpa only [triangleArrowContragredient_single_apply] using h

end ASGinzburg
