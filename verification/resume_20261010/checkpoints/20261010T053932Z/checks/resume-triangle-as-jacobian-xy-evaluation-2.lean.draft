import work.ASGinzburgDraft.TriangleASFoundationTensorRelations
import work.ASGinzburgDraft.TriangleASJacobianArrowBasisChange
import work.ASGinzburgDraft.TriangleJacobianArrowProducts
import work.ASGinzburgDraft.TriangleQuadraticTensorAction

/-! The chosen AS quadratic evaluation equals the actual canonical
Jacobian evaluation after the actual invertible X/Y basis changes. -/
namespace ASGinzburg
universe u

namespace ZAlgebra
variable {k : Type u} [Field k] (A : ZAlgebra.{u,u} k)

theorem ASRegular.triangleXYCoefficientEvaluation_single
    (hAS : A.ASRegular triangle333) (ij : Fin 3 × Fin 3) :
    hAS.triangleXYCoefficientEvaluation A (Pi.single ij 1) =
      A.comp (hAS.triangleYArrowEvaluation A (Pi.single ij.2 1))
        (hAS.triangleXArrowEvaluation A (Pi.single ij.1 1)) := by
  have hc := triangleXYCutComponentEquiv_arrowProduct_single k ij.1 ij.2 (1:k) (1:k)
  simp only [one_mul] at hc
  have hp : (triangleXYCutComponentEquiv k).symm (Pi.single ij 1) =
      triangle333.zeroCutPathComp k
        (triangleYArrowCutEquiv k (Pi.single ij.2 1))
        (triangleXArrowCutEquiv k (Pi.single ij.1 1)) := by
    rw [←hc,LinearEquiv.symm_apply_apply]
  change hAS.triangleXYPathEvaluation A
    ((triangleXYCutComponentEquiv k).symm (Pi.single ij 1)) = _
  rw [hp]
  exact hAS.triangleXYPathEvaluation_comp A _ _

end ZAlgebra

variable (k : Type u) [Field k] (φ : triangle333.Potential k)

theorem triangleASJacobianXYEvaluation_comp
    (hAS : (triangle333.unrolledJacobianZAlgebra k φ).ASRegular triangle333) :
    (triangleJacobianXYEvaluation k φ).comp
      (triangleQuadraticBasisChange k
        (triangleASJacobianXBasisChange k φ hAS)
        (triangleASJacobianYBasisChange k φ hAS)).toLinearMap =
          hAS.triangleXYCoefficientEvaluation (triangle333.unrolledJacobianZAlgebra k φ) := by
  have hSingle : ∀ ij : Fin 3 × Fin 3, triangleJacobianXYEvaluation k φ
      (triangleQuadraticBasisChange k (triangleASJacobianXBasisChange k φ hAS)
        (triangleASJacobianYBasisChange k φ hAS) (Pi.single ij 1)) =
          hAS.triangleXYCoefficientEvaluation (triangle333.unrolledJacobianZAlgebra k φ)
            (Pi.single ij 1) := by
    intro ij
    have hc : triangleQuadraticBasisChange k (triangleASJacobianXBasisChange k φ hAS)
        (triangleASJacobianYBasisChange k φ hAS) (Pi.single ij 1) =
          fun xy => triangleASJacobianXBasisChange k φ hAS (Pi.single ij.1 1) xy.1 *
            triangleASJacobianYBasisChange k φ hAS (Pi.single ij.2 1) xy.2 := by
      funext xy
      exact triangleQuadraticBasisChange_single k _ _ ij xy
    rw [hc,triangleJacobianXYEvaluation_arrowProduct,
      triangleASJacobianXBasisChange_commutes,triangleASJacobianYBasisChange_commutes]
    exact (hAS.triangleXYCoefficientEvaluation_single _ ij).symm
  have hBasis : ∀ ij : Fin 3 × Fin 3,
      ((triangleJacobianXYEvaluation k φ).comp
        (triangleQuadraticBasisChange k (triangleASJacobianXBasisChange k φ hAS)
          (triangleASJacobianYBasisChange k φ hAS)).toLinearMap)
            ((Pi.basisFun k (Fin 3 × Fin 3)) ij) =
        hAS.triangleXYCoefficientEvaluation (triangle333.unrolledJacobianZAlgebra k φ)
          ((Pi.basisFun k (Fin 3 × Fin 3)) ij) := by
    intro ij
    simpa only [Pi.basisFun_apply,LinearMap.comp_apply] using hSingle ij
  let result := (Pi.basisFun k (Fin 3 × Fin 3)).ext hBasis
  exact result

theorem triangleASJacobianXYEvaluation_basisChange
    (hAS : (triangle333.unrolledJacobianZAlgebra k φ).ASRegular triangle333)
    (c : Fin 3 × Fin 3 → k) :
    triangleJacobianXYEvaluation k φ
      (triangleQuadraticBasisChange k (triangleASJacobianXBasisChange k φ hAS)
        (triangleASJacobianYBasisChange k φ hAS) c) =
          hAS.triangleXYCoefficientEvaluation (triangle333.unrolledJacobianZAlgebra k φ) c :=
  LinearMap.congr_fun (triangleASJacobianXYEvaluation_comp k φ hAS) c

end ASGinzburg
