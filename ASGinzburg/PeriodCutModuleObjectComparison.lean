import ASGinzburg.PeriodCutCornerComponentComparison
import ASGinzburg.PeriodCutRecoveredRightModules

/-! Compare original and recovered components at the actual integer-indexed objects. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory Opposite
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

theorem cornerCoordinateObject_inverse (X : (E.cornerCoverZAlgebra Q).Obj) :
    E.cornerCoordinateObject Q (Q.heightEquiv.symm X.index)=X := by
  cases X
  simp only [cornerCoordinateObject,Equiv.apply_symm_apply]

noncomputable def cornerAtObjectEquiv (M : (E.cornerCoverZAlgebra Q).RightModule)
    (X : (E.cornerCoverZAlgebra Q).Obj) :
    M.obj.obj (op X) ≃ₗ[k]
      (E.cornerGradedRightModule Q M).componentSubmodule (Q.heightEquiv.symm X.index) :=
  (M.obj.mapIso (eqToIso (congrArg op (E.cornerCoordinateObject_inverse Q X)).symm)).toLinearEquiv.trans
      (E.cornerComponentEquiv Q M (Q.heightEquiv.symm X.index))

end ASGinzburg.ZAlgebra.PeriodIso
