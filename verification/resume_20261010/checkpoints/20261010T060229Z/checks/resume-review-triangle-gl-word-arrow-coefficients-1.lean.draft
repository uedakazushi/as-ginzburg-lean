import ASGinzburg.TriangleGLPathAutomorphism
import ASGinzburg.PathAutomorphismCyclicSubstitution
import work.ASGinzburgDraft.LinearCyclicDerivativeChainRule

/-! Actual triangle GL arrow substitutions have their genuine finite
linear word coefficients. This specializes the derived cyclic chain rule. -/
namespace ASGinzburg
universe u
variable (k : Type u) [Field k]

noncomputable def triangleGLWordArrowCoefficient (g : TriangleGL333 k)
    (a b : triangle333.Arrow) : k :=
  if triangle333.source b = triangle333.source a then
    triangleGLArrowMatrix k g (triangle333.source a)
      (Pi.single (triangleGLArrowIndex a) 1) (triangleGLArrowIndex b)
  else 0

theorem triangleEdgeArrowCoordinates_word (s : Fin 3) (x : ArrowSpace333 k) :
    triangle333.pathWordMap k s (triangleEdgeTarget s) (triangleEdgeArrowEquiv k s x).val =
      ∑ i : Fin 3, Finsupp.single [triangleEdgeArrow s i] (x i) := by
  classical
  have hx : x = ∑ i : Fin 3, Pi.single i (x i) := by
    ext i
    simp
  conv_lhs => rw [hx]
  simp only [map_sum,Submodule.coe_sum,triangleEdgeArrowEquiv_single,
    CutQuiver.pathWordMap,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,
    triangleEdgePath_toList]

theorem triangleGLPathAutomorphism_arrowReplacement (g : TriangleGL333 k)
    (a : triangle333.Arrow) :
    CutQuiver.VertexCutPathAutomorphism.arrowReplacement triangle333 k
      (triangleGLPathAutomorphism k g) a = triangleGLArrowReplacement k g a := by
  change CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k
    (triangleGLPathAutomorphism k g) _ _ (triangle333.pathIdentityArrowReplacement k a) = _
  rw [triangleGLPathAutomorphism_component]
  exact triangle333.pathArrowSubstitution_arrow k (triangleGLArrowReplacement k g) a

theorem triangleGLPathAutomorphism_wordArrowReplacement (g : TriangleGL333 k)
    (a : triangle333.Arrow) :
    CutQuiver.VertexCutPathAutomorphism.wordArrowReplacement triangle333 k
      (triangleGLPathAutomorphism k g) a =
        wordLinearArrowReplacement (triangleGLWordArrowCoefficient k g) a := by
  change triangle333.pathWordMap k _ _
    (CutQuiver.VertexCutPathAutomorphism.arrowReplacement triangle333 k
      (triangleGLPathAutomorphism k g) a) = _
  rw [triangleGLPathAutomorphism_arrowReplacement]
  change triangle333.pathWordMap k (triangle333.source a)
    (triangleEdgeTarget (triangle333.source a))
    (triangleEdgeArrowEquiv k (triangle333.source a)
      (triangleGLArrowMatrix k g (triangle333.source a)
        (Pi.single (triangleGLArrowIndex a) 1))).val = _
  rw [triangleEdgeArrowCoordinates_word]
  fin_cases a <;>
    simp [wordLinearArrowReplacement,triangleGLWordArrowCoefficient,
      triangleGLArrowIndex,triangle333,triangleEdgeArrow,Fin.sum_univ_succ]

theorem triangleGL_cyclicDerivative_chainRule (g : TriangleGL333 k)
    (b : triangle333.Arrow) (φ : triangle333.Potential k) :
    cyclicDerivative b
      (CutQuiver.VertexCutPathAutomorphism.potentialLinearEquiv triangle333 k
        (triangleGLPathAutomorphism k g) φ).val =
      ∑ a : triangle333.Arrow, triangleGLWordArrowCoefficient k g a b •
        wordSubstitution (wordLinearArrowReplacement (triangleGLWordArrowCoefficient k g))
          (cyclicDerivative a φ.val) := by
  rw [CutQuiver.VertexCutPathAutomorphism.potential_val_cyclicSubstitution]
  have he : CutQuiver.VertexCutPathAutomorphism.wordArrowReplacement triangle333 k
      (triangleGLPathAutomorphism k g) =
        wordLinearArrowReplacement (triangleGLWordArrowCoefficient k g) := by
    funext a
    exact triangleGLPathAutomorphism_wordArrowReplacement k g a
  rw [he]
  exact linear_cyclicDerivative_chainRule _ b φ.val

end ASGinzburg
