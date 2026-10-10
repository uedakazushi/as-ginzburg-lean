import work.ASGinzburgDraft.TriangleASFoundationTensorKernel
import work.ASGinzburgDraft.TriangleASIsomorphismArrowChanges
import work.ASGinzburgDraft.TriangleCutRelationBasisTransport
import ASGinzburg.TriangleTensorPathAutomorphismOrbits

/-! A vertex-fixed isomorphism of triangle AS-regular algebras preserves
the actual GL orbit of their foundation tensor candidates. No candidate
Ginzburg regularity is assumed. -/
namespace ASGinzburg
universe u
variable (k : Type u) [Field k] (A B : ZAlgebra.{u,u} k)
  (F : ZAlgebra.Isomorphism A B)
  (hAS : A.ASRegular triangle333) (hBS : B.ASRegular triangle333)

noncomputable def triangleASIsomorphismTransportedFoundationTensor : CubicTensor333 k :=
  arrowBasisChange333 k (triangleASIsomorphismXChange k A B F hAS hBS)
    (triangleASIsomorphismYChange k A B F hAS hBS) (LinearEquiv.refl k _)
    (hAS.triangleFoundationTensor A)

theorem triangleASIsomorphismTransportedFoundationTensor_cutRelations_linearIndependent :
    LinearIndependent k (tensorToCutRelations333 k
      (triangleASIsomorphismTransportedFoundationTensor k A B F hAS hBS)) := by
  let gX := triangleASIsomorphismXChange k A B F hAS hBS
  let gY := triangleASIsomorphismYChange k A B F hAS hBS
  have h := (hAS.triangleFoundationTensor_cutRelations_linearIndependent A).map'
    (triangleQuadraticBasisChange k gX gY).toLinearMap (triangleQuadraticBasisChange k gX gY).ker
  have he : (triangleQuadraticBasisChange k gX gY).toLinearMap ∘
      tensorToCutRelations333 k (hAS.triangleFoundationTensor A) =
      tensorToCutRelations333 k
        (triangleASIsomorphismTransportedFoundationTensor k A B F hAS hBS) := by
    funext z
    exact (triangleTensor_cutRelations_basisChangeXY k gX gY _ z).symm
  rw [he] at h
  exact h

theorem triangleASIsomorphismTransportedFoundationTensor_cutRelations_span :
    Submodule.span k (Set.range (tensorToCutRelations333 k
      (triangleASIsomorphismTransportedFoundationTensor k A B F hAS hBS))) =
    Submodule.span k (Set.range (tensorToCutRelations333 k (hBS.triangleFoundationTensor B))) := by
  have hle : Submodule.span k (Set.range (tensorToCutRelations333 k
      (triangleASIsomorphismTransportedFoundationTensor k A B F hAS hBS))) ≤
      LinearMap.ker (hBS.triangleXYCoefficientEvaluation B) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨z,rfl⟩
    change hBS.triangleXYCoefficientEvaluation B
      (tensorToCutRelations333 k
        (triangleASIsomorphismTransportedFoundationTensor k A B F hAS hBS) z) = 0
    rw [triangleASIsomorphismTransportedFoundationTensor,
      triangleTensor_cutRelations_basisChangeXY, triangleASIsomorphismXYEvaluation,
      hAS.triangleFoundationTensor_cutRelations_evaluation_zero A, map_zero]
  rw [←hBS.triangleFoundationTensor_cutRelations_span_eq_kernel B] at hle
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [finrank_span_eq_card
      (triangleASIsomorphismTransportedFoundationTensor_cutRelations_linearIndependent
        k A B F hAS hBS),
    finrank_span_eq_card (hBS.triangleFoundationTensor_cutRelations_linearIndependent B)]

include F

theorem triangleASRegular_Isomorphism_foundationTensor_orbit :
    ∃ g : TriangleGL333 k, g • hAS.triangleFoundationTensor A = hBS.triangleFoundationTensor B := by
  let gX := triangleASIsomorphismXChange k A B F hAS hBS
  let gY := triangleASIsomorphismYChange k A B F hAS hBS
  let t := triangleASIsomorphismTransportedFoundationTensor k A B F hAS hBS
  let w := hBS.triangleFoundationTensor B
  have ht := triangleASIsomorphismTransportedFoundationTensor_cutRelations_linearIndependent
    k A B F hAS hBS
  have hw := hBS.triangleFoundationTensor_cutRelations_linearIndependent B
  have hs := triangleASIsomorphismTransportedFoundationTensor_cutRelations_span k A B F hAS hBS
  let gZ := triangleArrowTranspose k (triangleCutRelationBasisChange k t w ht hw hs)
  have hz : arrowBasisChange333 k (LinearEquiv.refl k _) (LinearEquiv.refl k _) gZ t = w :=
    triangleTensor_eq_cutArrow_basisChange k t w ht hw hs
  let gXY : TriangleGL333 k := (gX,gY,LinearEquiv.refl k _)
  let gCut : TriangleGL333 k := (LinearEquiv.refl k _,LinearEquiv.refl k _,gZ)
  refine ⟨gCut * gXY,?_⟩
  rw [mul_smul]
  exact hz

theorem triangleASRegular_Isomorphism_foundationPotential_pathAutomorphism :
    ∃ E : triangle333.VertexCutPathAutomorphism k,
      CutQuiver.VertexCutPathAutomorphism.potentialLinearEquiv triangle333 k E
        (hAS.foundationPotential A triangle333) = hBS.foundationPotential B triangle333 := by
  have h := (triangleTensor_orbit_iff_pathAutomorphism k
    (hAS.triangleFoundationTensor A) (hBS.triangleFoundationTensor B)).mp
      (triangleASRegular_Isomorphism_foundationTensor_orbit k A B F hAS hBS)
  simpa only [ZAlgebra.ASRegular.triangleFoundationTensor, LinearEquiv.apply_symm_apply] using h

theorem triangleASRegular_Isomorphism_foundationPotential_pathClass :
    triangle333.potentialPathAutomorphismClass k (hAS.foundationPotential A triangle333) =
      triangle333.potentialPathAutomorphismClass k (hBS.foundationPotential B triangle333) := by
  rw [triangle333.potentialPathAutomorphismClass_eq_iff_smul]
  exact triangleASRegular_Isomorphism_foundationPotential_pathAutomorphism k A B F hAS hBS

end ASGinzburg
