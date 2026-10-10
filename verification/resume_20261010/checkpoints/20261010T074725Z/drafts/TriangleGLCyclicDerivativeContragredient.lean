import work.ASGinzburgDraft.TriangleGLWordMatrixInverse
import work.ASGinzburgDraft.LinearCyclicDerivativeInverseChainRule

/-! The actual triangle potential action has the actual contragredient
gradient transformation on each three-arrow endpoint block. -/
namespace ASGinzburg
universe u
variable (k : Type u) [Field k]

theorem triangleGL_wordDerivative_contragredient (g : TriangleGL333 k)
    (b : triangle333.Arrow) (φ : triangle333.Potential k) :
    wordSubstitution (wordLinearArrowReplacement (triangleGLWordArrowCoefficient k g))
      (cyclicDerivative b φ.val) =
      ∑ a : triangle333.Arrow, triangleGLWordArrowCoefficient k (g⁻¹) a b •
        cyclicDerivative a
          (CutQuiver.VertexCutPathAutomorphism.potentialLinearEquiv triangle333 k
            (triangleGLPathAutomorphism k g) φ).val := by
  have he : CutQuiver.VertexCutPathAutomorphism.wordArrowReplacement triangle333 k
      (triangleGLPathAutomorphism k g) =
        wordLinearArrowReplacement (triangleGLWordArrowCoefficient k g) := by
    funext a
    exact triangleGLPathAutomorphism_wordArrowReplacement k g a
  rw [CutQuiver.VertexCutPathAutomorphism.potential_val_cyclicSubstitution,he]
  exact linear_cyclicDerivative_inverse_chainRule _ _
    (triangleGLWordArrowCoefficient_inverse_sum k g) b φ.val

theorem triangleGL_wordDerivative_contragredient_block (g : TriangleGL333 k)
    (b : triangle333.Arrow) (φ : triangle333.Potential k) :
    wordSubstitution (wordLinearArrowReplacement (triangleGLWordArrowCoefficient k g))
      (cyclicDerivative b φ.val) =
      ∑ i : Fin 3,
        (triangleGLArrowMatrix k g (triangle333.source b)).symm
          (Pi.single i 1) (triangleGLArrowIndex b) •
          cyclicDerivative (triangleEdgeArrow (triangle333.source b) i)
            (CutQuiver.VertexCutPathAutomorphism.potentialLinearEquiv triangle333 k
              (triangleGLPathAutomorphism k g) φ).val := by
  classical
  rw [triangleGL_wordDerivative_contragredient,triangleArrow_sum]
  have hOnly :
      (∑ s : Fin 3, ∑ i : Fin 3,
        triangleGLWordArrowCoefficient k (g⁻¹) (triangleEdgeArrow s i) b •
          cyclicDerivative (triangleEdgeArrow s i)
            (CutQuiver.VertexCutPathAutomorphism.potentialLinearEquiv triangle333 k
              (triangleGLPathAutomorphism k g) φ).val) =
      ∑ i : Fin 3, triangleGLWordArrowCoefficient k (g⁻¹)
        (triangleEdgeArrow (triangle333.source b) i) b •
          cyclicDerivative (triangleEdgeArrow (triangle333.source b) i)
            (CutQuiver.VertexCutPathAutomorphism.potentialLinearEquiv triangle333 k
              (triangleGLPathAutomorphism k g) φ).val := by
    apply Finset.sum_eq_single (triangle333.source b)
    · intro s hs hsb
      apply Finset.sum_eq_zero
      intro i hi
      simp [triangleGLWordArrowCoefficient,triangleEdgeArrow_source,Ne.symm hsb]
    · simp
  rw [hOnly]
  simp only [triangleGLWordArrowCoefficient,triangleEdgeArrow_source,
    triangleEdgeArrow_index,ite_true,triangleGLArrowMatrix_inv]

end ASGinzburg
