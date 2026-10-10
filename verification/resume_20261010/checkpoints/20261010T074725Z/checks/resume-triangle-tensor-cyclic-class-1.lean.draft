import work.ASGinzburgDraft.TrianglePotentialCoordinates
import work.ASGinzburgDraft.TriangleArrowCoordinates
import work.ASGinzburgDraft.PotentialCyclicClass

/-! The actual triangle tensor corresponds to the actual closed-path
cyclic class of the product of its three arrow vectors. -/
namespace ASGinzburg
open scoped TensorProduct
universe u
variable (k : Type u) [Field k]

noncomputable def triangleArrowCycleTrilinearMap :
    ArrowSpace333 k →ₗ[k] ArrowSpace333 k →ₗ[k] ArrowSpace333 k →ₗ[k]
      AlgebraCyclicQuotient k (triangle333.PathRing k) where
  toFun x :=
    { toFun := fun y =>
        { toFun := fun z => triangle333.closedPathCyclicClass k 0
            (triangle333.pathComp k (triangleZArrowEquiv k z).val
              (triangle333.pathComp k (triangleYArrowEquiv k y).val
                (triangleXArrowEquiv k x).val))
          map_add' := by intro z z'; simp [map_add,LinearMap.add_apply]
          map_smul' := by intro a z; simp [map_smul,LinearMap.smul_apply] }
      map_add' := by intro y y'; apply LinearMap.ext; intro z; simp [map_add,LinearMap.add_apply]
      map_smul' := by intro a y; apply LinearMap.ext; intro z; simp [map_smul,LinearMap.smul_apply] }
  map_add' := by
    intro x x'
    apply LinearMap.ext
    intro y
    apply LinearMap.ext
    intro z
    simp [map_add,LinearMap.add_apply]
  map_smul' := by
    intro a x
    apply LinearMap.ext
    intro y
    apply LinearMap.ext
    intro z
    simp [map_smul,LinearMap.smul_apply]

noncomputable def triangleArrowCycleTensorMap :
    CubicTensor333 k →ₗ[k] AlgebraCyclicQuotient k (triangle333.PathRing k) :=
  TensorProduct.lift ((TensorProduct.uncurry k (ArrowSpace333 k) (ArrowSpace333 k)
    (AlgebraCyclicQuotient k (triangle333.PathRing k))).comp (triangleArrowCycleTrilinearMap k))

theorem triangleArrowCycleTensorMap_tmul (x y z : ArrowSpace333 k) :
    triangleArrowCycleTensorMap k (x ⊗ₜ[k] (y ⊗ₜ[k] z)) =
      triangle333.closedPathCyclicClass k 0
        (triangle333.pathComp k (triangleZArrowEquiv k z).val
          (triangle333.pathComp k (triangleYArrowEquiv k y).val
            (triangleXArrowEquiv k x).val)) := by
  simp [triangleArrowCycleTensorMap,triangleArrowCycleTrilinearMap]

theorem triangleTensorPotentialCyclicClass_basis (xyz : Triple333) :
    triangle333.potentialCyclicClass k (triangleTensorPotentialEquiv k (cubicBasis333 k xyz)) =
      triangle333.closedPathCyclicClass k 0
        (Finsupp.single ((triangleXPath xyz.1).comp (triangleYPath xyz.2.1) |>.comp
          (triangleZPath xyz.2.2)) 1) := by
  let p := ((triangleXPath xyz.1).comp (triangleYPath xyz.2.1)).comp (triangleZPath xyz.2.2)
  have hp : p = triangleCubicPath xyz := by
    apply CutQuiver.Path.toList_injective
    simp [p,CutQuiver.Path.toList_comp,triangleCubicPath,path_target_cast_toList,
      CutQuiver.Path.toList]
  have hc : p.cutDegree = 1 := by
    rw [hp]
    simp [triangleCubicPath,path_target_cast_cutDegree,CutQuiver.Path.cutDegree,
      CutQuiver.cutDegree,triangleX_cut,triangleY_cut,triangleZ_cut]
  have hl : 3 ≤ p.length := by
    rw [hp]
    simp [triangleCubicPath,path_target_cast_length,CutQuiver.Path.length]
  have hφ : triangleTensorPotentialEquiv k (cubicBasis333 k xyz) =
      (⟨traceWord (k:=k) p.toList,triangle333.traceWord_mem_potentialSpace k p hc hl⟩ :
        triangle333.Potential k) := by
    apply Subtype.ext
    rw [triangleTensorPotentialEquiv_basis_val]
    simp [p,traceWord,triangleCubicWordClass,CutQuiver.Path.toList_comp]
  rw [hφ]
  exact triangle333.potentialCyclicClass_traceWord k 0 p hc hl

theorem triangleArrowCycleTensorMap_eq :
    triangleArrowCycleTensorMap k = (triangle333.potentialCyclicClass k).comp
      (triangleTensorPotentialEquiv k).toLinearMap := by
  apply (cubicBasis333 k).ext
  intro xyz
  change triangleArrowCycleTensorMap k (cubicBasis333 k xyz) =
    triangle333.potentialCyclicClass k (triangleTensorPotentialEquiv k (cubicBasis333 k xyz))
  rw [triangleTensorPotentialCyclicClass_basis]
  simp [cubicBasis333,Module.Basis.tensorProduct_apply',Pi.basisFun_apply,
    triangleArrowCycleTensorMap_tmul,triangle333.pathComp_single]

theorem triangleTensorPotentialCyclicClass_tmul (x y z : ArrowSpace333 k) :
    triangle333.potentialCyclicClass k (triangleTensorPotentialEquiv k (x ⊗ₜ[k] (y ⊗ₜ[k] z))) =
      triangle333.closedPathCyclicClass k 0
        (triangle333.pathComp k (triangleZArrowEquiv k z).val
          (triangle333.pathComp k (triangleYArrowEquiv k y).val
            (triangleXArrowEquiv k x).val)) := by
  rw [← LinearMap.comp_apply,← triangleArrowCycleTensorMap_eq]
  exact triangleArrowCycleTensorMap_tmul k x y z

end ASGinzburg
