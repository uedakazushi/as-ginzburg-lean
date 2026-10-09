import ASGinzburg.FoundationTotalModules
import Mathlib.Algebra.Category.ModuleCat.Algebra

/-! Restricting the genuine total-ring module to k gives precisely
the original componentwise vector-space structure, linearly. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
open scoped ModuleCat.Algebra
attribute [local instance 2000] ModuleCat.isModule
universe u
variable {k : Type u} [Field k] (A : ZAlgebra.{u,u} k) (Q : CutQuiver)

theorem foundationRightTotalModule_scalar_smul (M : A.FoundationRightModule Q)
    (c : k) (m : A.foundationRightTotalModule Q M) :
    c • m=(fun i : Q.Vertex => c • m i) := by
  change A.foundationRightTotalUnitalRepresentation Q M
    (algebraMap k (A.FoundationAlgebra Q)ᵐᵒᵖ c) m=_
  rw [AlgHom.commutes,Module.algebraMap_end_apply]
  rfl

noncomputable def foundationRightTotalUnderlyingLinearEquiv (M : A.FoundationRightModule Q) :
    (A.foundationRightTotalModule Q M) ≃ₗ[k] A.foundationRightTotalSpace Q M where
  toFun := fun m => m
  invFun := fun m => m
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c m := A.foundationRightTotalModule_scalar_smul Q M c m

end ASGinzburg.ZAlgebra
