import work.ASGinzburgDraft.TriangleCutZRelationBasis
import work.ASGinzburgDraft.TriangleCutZDerivativeCoordinates

/-! The original tensor's cut slices are independent under the genuine
Ginzburg regularity condition, by the actual Jacobian relation basis. -/
namespace ASGinzburg
universe u v w

theorem submoduleBasis_val_linearIndependent
    {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
    {ι : Type w} (S : Submodule k V) (b : Module.Basis ι k S) :
    LinearIndependent k (fun i => (b i).val) :=
  b.linearIndependent.map' S.subtype (Submodule.ker_subtype S)

variable (k : Type u) [Field k]

theorem triangleCutZDerivative_linearIndependent (φ : triangle333.Potential k)
    (hG : triangle333.GinzburgRegular k φ) :
    LinearIndependent k (triangleCutZDerivative k φ) := by
  have h := submoduleBasis_val_linearIndependent
    (triangle333.pathJacobianCutIdeal k φ 0 2 0) (triangleCutZRelationBasis k φ hG)
  have hb : (fun z => (triangleCutZRelationBasis k φ hG z).val) =
      triangleCutZDerivative k φ := by
    funext z
    rw [triangleCutZRelationBasis_apply]
    rfl
  rw [hb] at h
  exact h

theorem triangleGinzburgRegular_tensorCutRelations_linearIndependent (w : CubicTensor333 k)
    (hG : triangle333.GinzburgRegular k (triangleTensorPotentialEquiv k w)) :
    LinearIndependent k (tensorToCutRelations333 k w) := by
  have h := triangleCutZDerivative_linearIndependent k (triangleTensorPotentialEquiv k w) hG
  have hm := h.map' (triangleXYCutComponentEquiv k).toLinearMap
    (triangleXYCutComponentEquiv k).ker
  have he : (triangleXYCutComponentEquiv k).toLinearMap ∘
      triangleCutZDerivative k (triangleTensorPotentialEquiv k w) =
        tensorToCutRelations333 k w := by
    funext z
    exact triangleTensorPotential_cutZDerivative_coordinates k w z
  rw [he] at hm
  exact hm

theorem triangleGinzburgRegular_originalTensorCutRelations_linearIndependent
    (φ : triangle333.Potential k) (hG : triangle333.GinzburgRegular k φ) :
    LinearIndependent k (tensorToCutRelations333 k ((triangleTensorPotentialEquiv k).symm φ)) := by
  apply triangleGinzburgRegular_tensorCutRelations_linearIndependent k
  simpa only [LinearEquiv.apply_symm_apply] using hG

end ASGinzburg
