import work.ASGinzburgDraft.TriangleGinzburgRegularActions
import ASGinzburg.Corollary52QuotientEquivalence
import Mathlib.GroupTheory.GroupAction.Hom

/-! The actual tensor-potential equivalence intertwines the proved
regular-subtype actions through the genuine triangle GL group isomorphism. -/
namespace ASGinzburg
universe u
variable (k : Type u) [Field k]

theorem triangleRegularTensorPotentialEquiv_GL_smul (g : TriangleGL333 k)
    (w : GinzburgRegularTensor333 k) :
    ginzburgRegularTensorPotentialEquiv333 k (g • w) =
      triangleGLPathAutomorphism k g • ginzburgRegularTensorPotentialEquiv333 k w := by
  apply Subtype.ext
  change triangleTensorPotentialEquiv k (g • w.val) =
    CutQuiver.VertexCutPathAutomorphism.potentialLinearEquiv triangle333 k
      (triangleGLPathAutomorphism k g) (triangleTensorPotentialEquiv k w.val)
  rw [trianglePathAutomorphism_tensorPotential,trianglePathAutomorphismGLTriple_extension]
  rfl

theorem triangleRegularTensorPotentialEquiv_pathAutomorphism_smul
    (E : triangle333.VertexCutPathAutomorphism k) (w : GinzburgRegularTensor333 k) :
    ginzburgRegularTensorPotentialEquiv333 k
        (trianglePathAutomorphismGLTriple k E • w) =
      E • ginzburgRegularTensorPotentialEquiv333 k w := by
  simpa only [triangleGLPathAutomorphism_restriction] using
    triangleRegularTensorPotentialEquiv_GL_smul k (trianglePathAutomorphismGLTriple k E) w

noncomputable def triangleRegularTensorPotentialActionHom :
    GinzburgRegularTensor333 k →ₑ[(trianglePathAutomorphismGLEquiv k).symm]
      GinzburgRegularPotential k triangle333 where
  toFun := ginzburgRegularTensorPotentialEquiv333 k
  map_smul' := triangleRegularTensorPotentialEquiv_GL_smul k

end ASGinzburg
