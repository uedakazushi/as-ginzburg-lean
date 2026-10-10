import work.ASGinzburgDraft.TriangleASJacobianXYEvaluation
import work.ASGinzburgDraft.TriangleCutRelationBasisTransport
import work.ASGinzburgDraft.TriangleCutZSliceIndependence
import work.ASGinzburgDraft.TriangleTensorPathAutomorphismOrbits

/-! The genuine source composition Φ → A(Φ) → Φ_B recovers every
original Ginzburg-regular triangle potential up to an actual path
automorphism, with no regularity or recovery premise on the candidate. -/
namespace ASGinzburg
universe u
variable (k : Type u) [Field k]

noncomputable def triangleGinzburgFoundationTensorInOriginalCoordinates
    (φ : triangle333.Potential k) (hG : triangle333.GinzburgRegular k φ) : CubicTensor333 k :=
  arrowBasisChange333 k
    (triangleASJacobianXBasisChange k φ (hG.asRegular triangle333 k φ))
    (triangleASJacobianYBasisChange k φ (hG.asRegular triangle333 k φ))
    (LinearEquiv.refl k _)
    ((hG.asRegular triangle333 k φ).triangleFoundationTensor _)

theorem triangleGinzburgFoundationTensorInOriginalCoordinates_cutRelations_linearIndependent
    (φ : triangle333.Potential k) (hG : triangle333.GinzburgRegular k φ) :
    LinearIndependent k (tensorToCutRelations333 k
      (triangleGinzburgFoundationTensorInOriginalCoordinates k φ hG)) := by
  let hAS := hG.asRegular triangle333 k φ
  let gX := triangleASJacobianXBasisChange k φ hAS
  let gY := triangleASJacobianYBasisChange k φ hAS
  have h := (hAS.triangleFoundationTensor_cutRelations_linearIndependent _).map'
    (triangleQuadraticBasisChange k gX gY).toLinearMap (triangleQuadraticBasisChange k gX gY).ker
  have he : (triangleQuadraticBasisChange k gX gY).toLinearMap ∘
      tensorToCutRelations333 k (hAS.triangleFoundationTensor _) =
      tensorToCutRelations333 k (triangleGinzburgFoundationTensorInOriginalCoordinates k φ hG) := by
    funext z
    exact (triangleTensor_cutRelations_basisChangeXY k gX gY _ z).symm
  rw [he] at h
  exact h

theorem triangleGinzburgFoundationTensorInOriginalCoordinates_cutRelations_span
    (φ : triangle333.Potential k) (hG : triangle333.GinzburgRegular k φ) :
    Submodule.span k (Set.range (tensorToCutRelations333 k
      (triangleGinzburgFoundationTensorInOriginalCoordinates k φ hG))) =
    Submodule.span k (Set.range (tensorToCutRelations333 k
      ((triangleTensorPotentialEquiv k).symm φ))) := by
  have hle : Submodule.span k (Set.range (tensorToCutRelations333 k
      (triangleGinzburgFoundationTensorInOriginalCoordinates k φ hG))) ≤
      LinearMap.ker (triangleJacobianXYEvaluation k φ) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨z,rfl⟩
    change triangleJacobianXYEvaluation k φ
      (tensorToCutRelations333 k (triangleGinzburgFoundationTensorInOriginalCoordinates k φ hG) z) = 0
    rw [triangleGinzburgFoundationTensorInOriginalCoordinates,
      triangleTensor_cutRelations_basisChangeXY,
      triangleASJacobianXYEvaluation_basisChange]
    exact (hG.asRegular triangle333 k φ).triangleFoundationTensor_cutRelations_evaluation_zero _ z
  rw [triangleJacobianXYEvaluation_kernel_eq_tensorSlices] at hle
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [finrank_span_eq_card
      (triangleGinzburgFoundationTensorInOriginalCoordinates_cutRelations_linearIndependent k φ hG),
    finrank_span_eq_card
      (triangleGinzburgRegular_originalTensorCutRelations_linearIndependent k φ hG)]

theorem triangleGinzburgRegular_foundationTensor_GL_orbit
    (φ : triangle333.Potential k) (hG : triangle333.GinzburgRegular k φ) :
    ∃ g : TriangleGL333 k,
      g • ((hG.asRegular triangle333 k φ).triangleFoundationTensor _) =
        (triangleTensorPotentialEquiv k).symm φ := by
  let hAS := hG.asRegular triangle333 k φ
  let gX := triangleASJacobianXBasisChange k φ hAS
  let gY := triangleASJacobianYBasisChange k φ hAS
  let t := triangleGinzburgFoundationTensorInOriginalCoordinates k φ hG
  let w := (triangleTensorPotentialEquiv k).symm φ
  have ht := triangleGinzburgFoundationTensorInOriginalCoordinates_cutRelations_linearIndependent k φ hG
  have hw := triangleGinzburgRegular_originalTensorCutRelations_linearIndependent k φ hG
  have hs := triangleGinzburgFoundationTensorInOriginalCoordinates_cutRelations_span k φ hG
  let gZ := triangleArrowTranspose k (triangleCutRelationBasisChange k t w ht hw hs)
  have hz : arrowBasisChange333 k (LinearEquiv.refl k _) (LinearEquiv.refl k _) gZ t = w :=
    triangleTensor_eq_cutArrow_basisChange k t w ht hw hs
  let gXY : TriangleGL333 k := (gX,gY,LinearEquiv.refl k _)
  let gCut : TriangleGL333 k := (LinearEquiv.refl k _,LinearEquiv.refl k _,gZ)
  refine ⟨gCut * gXY,?_⟩
  rw [mul_smul]
  exact hz

theorem triangleGinzburgRegular_foundationPotential_pathAutomorphism
    (φ : triangle333.Potential k) (hG : triangle333.GinzburgRegular k φ) :
    ∃ E : triangle333.VertexCutPathAutomorphism k,
      CutQuiver.VertexCutPathAutomorphism.potentialLinearEquiv triangle333 k E
        ((hG.asRegular triangle333 k φ).foundationPotential _ triangle333) = φ := by
  have h := (triangleTensor_orbit_iff_pathAutomorphism k
    ((hG.asRegular triangle333 k φ).triangleFoundationTensor _)
    ((triangleTensorPotentialEquiv k).symm φ)).mp
      (triangleGinzburgRegular_foundationTensor_GL_orbit k φ hG)
  simpa only [ZAlgebra.ASRegular.triangleFoundationTensor,LinearEquiv.apply_symm_apply] using h

theorem triangleGinzburgRegular_foundationPotential_pathClass
    (φ : triangle333.Potential k) (hG : triangle333.GinzburgRegular k φ) :
    triangle333.potentialPathAutomorphismClass k
      ((hG.asRegular triangle333 k φ).foundationPotential _ triangle333) =
        triangle333.potentialPathAutomorphismClass k φ := by
  rw [triangle333.potentialPathAutomorphismClass_eq_iff_smul]
  exact triangleGinzburgRegular_foundationPotential_pathAutomorphism k φ hG

end ASGinzburg
