import work.ASGinzburgDraft.TriangleCutSliceAction
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! Two actual bases of the same quadratic relation subspace are related
by a genuine invertible cut-arrow change, using the actual tensor action. -/
namespace ASGinzburg
universe u
variable (k : Type u) [Field k]

noncomputable def triangleCutRelationLinearMap (w : CubicTensor333 k) :
    ArrowSpace333 k →ₗ[k] (Fin 3 × Fin 3 → k) :=
  (Pi.basisFun k (Fin 3)).constr k (tensorToCutRelations333 k w)

theorem triangleCutRelationLinearMap_single (w : CubicTensor333 k) (z : Fin 3) :
    triangleCutRelationLinearMap k w (Pi.single z 1) = tensorToCutRelations333 k w z := by
  simpa only [triangleCutRelationLinearMap, Pi.basisFun_apply] using
    (Pi.basisFun k (Fin 3)).constr_basis k (tensorToCutRelations333 k w) z

theorem triangleCutRelationLinearMap_range (w : CubicTensor333 k) :
    LinearMap.range (triangleCutRelationLinearMap k w) =
      Submodule.span k (Set.range (tensorToCutRelations333 k w)) :=
  (Pi.basisFun k (Fin 3)).constr_range k

theorem triangleCutRelationLinearMap_injective (w : CubicTensor333 k)
    (hw : LinearIndependent k (tensorToCutRelations333 k w)) :
    Function.Injective (triangleCutRelationLinearMap k w) := by
  apply LinearMap.injective_of_linearIndependent (Pi.basisFun k (Fin 3)).span_eq
  simpa only [Function.comp_def, Pi.basisFun_apply,
    triangleCutRelationLinearMap_single] using hw

noncomputable def triangleCutRelationBasisChange (w w' : CubicTensor333 k)
    (hw : LinearIndependent k (tensorToCutRelations333 k w))
    (hw' : LinearIndependent k (tensorToCutRelations333 k w'))
    (hspan : Submodule.span k (Set.range (tensorToCutRelations333 k w)) =
      Submodule.span k (Set.range (tensorToCutRelations333 k w'))) :
    ArrowSpace333 k ≃ₗ[k] ArrowSpace333 k :=
  (LinearEquiv.ofInjective (triangleCutRelationLinearMap k w')
    (triangleCutRelationLinearMap_injective k w' hw')).trans
    ((LinearEquiv.ofEq _ _ (by simpa only [triangleCutRelationLinearMap_range] using hspan.symm)).trans
      (LinearEquiv.ofInjective (triangleCutRelationLinearMap k w)
        (triangleCutRelationLinearMap_injective k w hw)).symm)

theorem triangleCutRelationBasisChange_commutes (w w' : CubicTensor333 k)
    (hw : LinearIndependent k (tensorToCutRelations333 k w))
    (hw' : LinearIndependent k (tensorToCutRelations333 k w'))
    (hspan : Submodule.span k (Set.range (tensorToCutRelations333 k w)) =
      Submodule.span k (Set.range (tensorToCutRelations333 k w')))
    (x : ArrowSpace333 k) :
    triangleCutRelationLinearMap k w (triangleCutRelationBasisChange k w w' hw hw' hspan x) =
      triangleCutRelationLinearMap k w' x := by
  let e := LinearEquiv.ofInjective (triangleCutRelationLinearMap k w)
    (triangleCutRelationLinearMap_injective k w hw)
  have h := congrArg Subtype.val (e.apply_symm_apply
    (LinearEquiv.ofEq _ _ (by simpa only [triangleCutRelationLinearMap_range] using hspan.symm)
      (LinearEquiv.ofInjective (triangleCutRelationLinearMap k w')
        (triangleCutRelationLinearMap_injective k w' hw') x)))
  exact h

theorem triangleTensor_eq_cutArrow_basisChange (w w' : CubicTensor333 k)
    (hw : LinearIndependent k (tensorToCutRelations333 k w))
    (hw' : LinearIndependent k (tensorToCutRelations333 k w'))
    (hspan : Submodule.span k (Set.range (tensorToCutRelations333 k w)) =
      Submodule.span k (Set.range (tensorToCutRelations333 k w'))) :
    arrowBasisChange333 k (LinearEquiv.refl k _) (LinearEquiv.refl k _)
      (triangleArrowTranspose k (triangleCutRelationBasisChange k w w' hw hw' hspan)) w = w' := by
  apply (tensorToCutRelations333 k).injective
  funext z xy
  rw [tensorToCutRelations333_basisChangeZ]
  have h := congrFun (triangleCutRelationBasisChange_commutes k w w' hw hw' hspan
    (Pi.single z 1)) xy
  rw [triangleCutRelationLinearMap_single] at h
  simpa only [triangleCutRelationLinearMap, Module.Basis.constr_apply_fintype,
    Module.Basis.equivFun_apply, Pi.basisFun_repr, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] using h

end ASGinzburg
