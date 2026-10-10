import work.ASGinzburgDraft.TriangleASJacobianXYEvaluation
import ASGinzburg.ZAlgebraIsomorphisms

/-! An actual vertex-fixed AS-algebra isomorphism induces actual
invertible changes of the chosen X/Y arrow coordinates and intertwines
the genuine quadratic evaluation maps. No candidate regularity is used. -/
namespace ASGinzburg
universe u

namespace ZAlgebra
variable {k : Type u} [Field k] (A : ZAlgebra.{u,u} k)

theorem ASRegular.triangleXYCoefficientEvaluation_arrowProduct
    (hAS : A.ASRegular triangle333) (x y : ArrowSpace333 k) :
    hAS.triangleXYCoefficientEvaluation A (fun ij => x ij.1 * y ij.2) =
      A.comp (hAS.triangleYArrowEvaluation A y) (hAS.triangleXArrowEvaluation A x) := by
  have hc := triangleXYCutComponentEquiv_arrowProduct k x y
  have hp : (triangleXYCutComponentEquiv k).symm (fun ij => x ij.1 * y ij.2) =
      triangle333.zeroCutPathComp k (triangleYArrowCutEquiv k y) (triangleXArrowCutEquiv k x) := by
    rw [←hc,LinearEquiv.symm_apply_apply]
  change hAS.triangleXYPathEvaluation A
    ((triangleXYCutComponentEquiv k).symm (fun ij => x ij.1 * y ij.2)) = _
  rw [hp]
  exact hAS.triangleXYPathEvaluation_comp A x y

end ZAlgebra

variable (k : Type u) [Field k] (A B : ZAlgebra.{u,u} k)
  (F : ZAlgebra.Isomorphism A B) (hAS : A.ASRegular triangle333) (hBS : B.ASRegular triangle333)

noncomputable def triangleASIsomorphismXChange : ArrowSpace333 k ≃ₗ[k] ArrowSpace333 k :=
  ((hAS.triangleXArrowEvaluationEquiv A).trans (F.map 0 1)).trans
    (hBS.triangleXArrowEvaluationEquiv B).symm

noncomputable def triangleASIsomorphismYChange : ArrowSpace333 k ≃ₗ[k] ArrowSpace333 k :=
  ((hAS.triangleYArrowEvaluationEquiv A).trans (F.map 1 2)).trans
    (hBS.triangleYArrowEvaluationEquiv B).symm

theorem triangleASIsomorphismXChange_commutes (x : ArrowSpace333 k) :
    hBS.triangleXArrowEvaluation B (triangleASIsomorphismXChange k A B F hAS hBS x) =
      F.map 0 1 (hAS.triangleXArrowEvaluation A x) :=
  (hBS.triangleXArrowEvaluationEquiv B).apply_symm_apply _

theorem triangleASIsomorphismYChange_commutes (y : ArrowSpace333 k) :
    hBS.triangleYArrowEvaluation B (triangleASIsomorphismYChange k A B F hAS hBS y) =
      F.map 1 2 (hAS.triangleYArrowEvaluation A y) :=
  (hBS.triangleYArrowEvaluationEquiv B).apply_symm_apply _

theorem triangleASIsomorphismXYEvaluation (c : Fin 3 × Fin 3 → k) :
    hBS.triangleXYCoefficientEvaluation B
        (triangleQuadraticBasisChange k (triangleASIsomorphismXChange k A B F hAS hBS)
          (triangleASIsomorphismYChange k A B F hAS hBS) c) =
      F.map 0 2 (hAS.triangleXYCoefficientEvaluation A c) := by
  let L := (hBS.triangleXYCoefficientEvaluation B).comp
    (triangleQuadraticBasisChange k (triangleASIsomorphismXChange k A B F hAS hBS)
      (triangleASIsomorphismYChange k A B F hAS hBS)).toLinearMap
  let R := (F.map 0 2).toLinearMap.comp (hAS.triangleXYCoefficientEvaluation A)
  have hSingle : ∀ ij : Fin 3 × Fin 3, L (Pi.single ij 1) = R (Pi.single ij 1) := by
    intro ij
    change hBS.triangleXYCoefficientEvaluation B
        (triangleQuadraticBasisChange k (triangleASIsomorphismXChange k A B F hAS hBS)
          (triangleASIsomorphismYChange k A B F hAS hBS) (Pi.single ij 1)) =
      F.map 0 2 (hAS.triangleXYCoefficientEvaluation A (Pi.single ij 1))
    have hc : triangleQuadraticBasisChange k (triangleASIsomorphismXChange k A B F hAS hBS)
        (triangleASIsomorphismYChange k A B F hAS hBS) (Pi.single ij 1) =
      fun xy => triangleASIsomorphismXChange k A B F hAS hBS (Pi.single ij.1 1) xy.1 *
        triangleASIsomorphismYChange k A B F hAS hBS (Pi.single ij.2 1) xy.2 := by
      funext xy
      exact triangleQuadraticBasisChange_single k _ _ ij xy
    rw [hc,hBS.triangleXYCoefficientEvaluation_arrowProduct B,
      triangleASIsomorphismXChange_commutes,triangleASIsomorphismYChange_commutes,
      hAS.triangleXYCoefficientEvaluation_single A,F.map_comp]
  have hBasis : ∀ ij : Fin 3 × Fin 3,
      L (Pi.basisFun k (Fin 3 × Fin 3) ij) = R (Pi.basisFun k (Fin 3 × Fin 3) ij) := by
    simpa only [Pi.basisFun_apply] using hSingle
  let result := (Pi.basisFun k (Fin 3 × Fin 3)).ext hBasis
  exact LinearMap.congr_fun result c

end ASGinzburg
