import ASGinzburg.TriangleTensorCyclicClass
import ASGinzburg.TrianglePathAutomorphismArrowMatrices
import ASGinzburg.PotentialPathAutomorphismAction
import ASGinzburg.PathAutomorphismLengthFiltration

/-! The genuine triangle path-algebra action on actual potentials is
the usual tensor action of its three actual arrow-space automorphisms. -/
namespace ASGinzburg
open scoped TensorProduct
universe u
variable (k : Type u) [Field k]

theorem trianglePathAutomorphism_tensorCyclicClass_tmul
    (E : triangle333.VertexCutPathAutomorphism k) (x y z : ArrowSpace333 k) :
    algebraCyclicEquiv k E.val
        (triangle333.potentialCyclicClass k
          (triangleTensorPotentialEquiv k (x ⊗ₜ[k] (y ⊗ₜ[k] z)))) =
      triangle333.potentialCyclicClass k
        (triangleTensorPotentialEquiv k
          (triangleTensorRepresentation k (trianglePathAutomorphismGLTriple k E)
            (x ⊗ₜ[k] (y ⊗ₜ[k] z)))) := by
  let e := CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k E
  have hXY : e 0 2 (triangle333.pathComp k (triangleYArrowEquiv k y).val
      (triangleXArrowEquiv k x).val) =
      triangle333.pathComp k (e 1 2 (triangleYArrowEquiv k y).val)
        (e 0 1 (triangleXArrowEquiv k x).val) :=
    triangle333.pathAlgEquivComponent_pathComp k E.val
      (CutQuiver.VertexCutPathAutomorphism.fixes_vertex triangle333 k E) _ _
  have hXYZ : e 0 0 (triangle333.pathComp k (triangleZArrowEquiv k z).val
      (triangle333.pathComp k (triangleYArrowEquiv k y).val (triangleXArrowEquiv k x).val)) =
      triangle333.pathComp k (e 2 0 (triangleZArrowEquiv k z).val)
        (e 0 2 (triangle333.pathComp k (triangleYArrowEquiv k y).val
          (triangleXArrowEquiv k x).val)) :=
    triangle333.pathAlgEquivComponent_pathComp k E.val
      (CutQuiver.VertexCutPathAutomorphism.fixes_vertex triangle333 k E) _ _
  change _ = triangle333.potentialCyclicClass k (triangleTensorPotentialEquiv k
    (arrowBasisChange333 k (trianglePathAutomorphismGLTriple k E).1
      (trianglePathAutomorphismGLTriple k E).2.1 (trianglePathAutomorphismGLTriple k E).2.2
      (x ⊗ₜ[k] (y ⊗ₜ[k] z))))
  rw [arrowBasisChange333_tmul,triangleTensorPotentialCyclicClass_tmul,
    triangleTensorPotentialCyclicClass_tmul,
    CutQuiver.VertexCutPathAutomorphism.cyclicEquiv_closedPathClass]
  change triangle333.closedPathCyclicClass k 0 (e 0 0 _) = _
  rw [hXYZ,hXY,← trianglePathAutomorphismGLTriple_Z_coordinates k E z,
    ← trianglePathAutomorphismGLTriple_Y_coordinates k E y,
    ← trianglePathAutomorphismGLTriple_X_coordinates k E x]

theorem trianglePathAutomorphism_tensorCyclicClass_map
    (E : triangle333.VertexCutPathAutomorphism k) :
    (algebraCyclicEquiv k E.val).toLinearMap.comp
        ((triangle333.potentialCyclicClass k).comp (triangleTensorPotentialEquiv k).toLinearMap) =
      ((triangle333.potentialCyclicClass k).comp (triangleTensorPotentialEquiv k).toLinearMap).comp
        (triangleTensorRepresentation k (trianglePathAutomorphismGLTriple k E)).toLinearMap := by
  apply (cubicBasis333 k).ext
  intro xyz
  simp only [LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,cubicBasis333,
    Module.Basis.tensorProduct_apply']
  exact trianglePathAutomorphism_tensorCyclicClass_tmul k E _ _ _

theorem trianglePathAutomorphism_tensorCyclicClass
    (E : triangle333.VertexCutPathAutomorphism k) (w : CubicTensor333 k) :
    algebraCyclicEquiv k E.val
        (triangle333.potentialCyclicClass k (triangleTensorPotentialEquiv k w)) =
      triangle333.potentialCyclicClass k
        (triangleTensorPotentialEquiv k
          (triangleTensorRepresentation k (trianglePathAutomorphismGLTriple k E) w)) :=
  LinearMap.congr_fun (trianglePathAutomorphism_tensorCyclicClass_map k E) w

theorem trianglePathAutomorphism_tensorPotential
    (E : triangle333.VertexCutPathAutomorphism k) (w : CubicTensor333 k) :
    CutQuiver.VertexCutPathAutomorphism.potentialLinearEquiv triangle333 k E
        (triangleTensorPotentialEquiv k w) =
      triangleTensorPotentialEquiv k
        (triangleTensorRepresentation k (trianglePathAutomorphismGLTriple k E) w) := by
  apply triangle333.potentialCyclicClass_injective k
  exact (CutQuiver.VertexCutPathAutomorphism.potentialLinearEquiv_cyclicClass
    triangle333 k E (triangleTensorPotentialEquiv k w)).trans
      (trianglePathAutomorphism_tensorCyclicClass k E w)

end ASGinzburg
