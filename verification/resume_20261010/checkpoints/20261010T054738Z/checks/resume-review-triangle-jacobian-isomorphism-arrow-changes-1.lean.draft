import work.ASGinzburgDraft.TriangleJacobianArrowProducts
import work.ASGinzburgDraft.TriangleQuadraticTensorAction
import ASGinzburg.ZAlgebraIsomorphisms

/-! A genuine vertex-fixed isomorphism of triangle Jacobian Z-algebras
induces actual invertible arrow changes and intertwines quadratic evaluation. -/
namespace ASGinzburg
universe u
variable (k : Type u) [Field k] (φ ψ : triangle333.Potential k)
  (F : ZAlgebra.Isomorphism (triangle333.unrolledJacobianZAlgebra k φ)
    (triangle333.unrolledJacobianZAlgebra k ψ))

noncomputable def triangleJacobianIsomorphismXChange :
    ArrowSpace333 k ≃ₗ[k] ArrowSpace333 k :=
  ((triangleJacobianXArrowEquiv k φ).trans (F.map 0 1)).trans
    (triangleJacobianXArrowEquiv k ψ).symm

noncomputable def triangleJacobianIsomorphismYChange :
    ArrowSpace333 k ≃ₗ[k] ArrowSpace333 k :=
  ((triangleJacobianYArrowEquiv k φ).trans (F.map 1 2)).trans
    (triangleJacobianYArrowEquiv k ψ).symm

theorem triangleJacobianIsomorphismXChange_commutes (x : ArrowSpace333 k) :
    triangleJacobianXArrowEquiv k ψ (triangleJacobianIsomorphismXChange k φ ψ F x) =
      F.map 0 1 (triangleJacobianXArrowEquiv k φ x) :=
  (triangleJacobianXArrowEquiv k ψ).apply_symm_apply _

theorem triangleJacobianIsomorphismYChange_commutes (y : ArrowSpace333 k) :
    triangleJacobianYArrowEquiv k ψ (triangleJacobianIsomorphismYChange k φ ψ F y) =
      F.map 1 2 (triangleJacobianYArrowEquiv k φ y) :=
  (triangleJacobianYArrowEquiv k ψ).apply_symm_apply _

theorem triangleJacobianIsomorphismXYEvaluation (c : Fin 3 × Fin 3 → k) :
    triangleJacobianXYEvaluation k ψ
      (triangleQuadraticBasisChange k (triangleJacobianIsomorphismXChange k φ ψ F)
        (triangleJacobianIsomorphismYChange k φ ψ F) c) =
      F.map 0 2 (triangleJacobianXYEvaluation k φ c) := by
  let L := (triangleJacobianXYEvaluation k ψ).comp
    (triangleQuadraticBasisChange k (triangleJacobianIsomorphismXChange k φ ψ F)
      (triangleJacobianIsomorphismYChange k φ ψ F)).toLinearMap
  let R := (F.map 0 2).toLinearMap.comp (triangleJacobianXYEvaluation k φ)
  have hSingle : ∀ ij : Fin 3 × Fin 3, L (Pi.single ij 1) = R (Pi.single ij 1) := by
    intro ij
    change triangleJacobianXYEvaluation k ψ
      (triangleQuadraticBasisChange k (triangleJacobianIsomorphismXChange k φ ψ F)
        (triangleJacobianIsomorphismYChange k φ ψ F) (Pi.single ij 1)) =
      F.map 0 2 (triangleJacobianXYEvaluation k φ (Pi.single ij 1))
    have hc : triangleQuadraticBasisChange k (triangleJacobianIsomorphismXChange k φ ψ F)
        (triangleJacobianIsomorphismYChange k φ ψ F) (Pi.single ij 1) =
      fun xy => triangleJacobianIsomorphismXChange k φ ψ F (Pi.single ij.1 1) xy.1 *
        triangleJacobianIsomorphismYChange k φ ψ F (Pi.single ij.2 1) xy.2 := by
      funext xy
      exact triangleQuadraticBasisChange_single k _ _ ij xy
    rw [hc,triangleJacobianXYEvaluation_arrowProduct,
      triangleJacobianIsomorphismXChange_commutes,triangleJacobianIsomorphismYChange_commutes,
      triangleJacobianXYEvaluation_single,F.map_comp]
    rw [←triangleJacobianXArrowEquiv_single,←triangleJacobianYArrowEquiv_single]
  have hBasis : ∀ ij : Fin 3 × Fin 3,
      L (Pi.basisFun k (Fin 3 × Fin 3) ij) = R (Pi.basisFun k (Fin 3 × Fin 3) ij) := by
    simpa only [Pi.basisFun_apply] using hSingle
  let result := (Pi.basisFun k (Fin 3 × Fin 3)).ext hBasis
  exact LinearMap.congr_fun result c

end ASGinzburg
