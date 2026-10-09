import ASGinzburg.PeriodCutModuleUnitNaturality
import ASGinzburg.PeriodCutRecoveredModuleFunctor

/-! Passing a cover module to its genuine graded R module and recovering
the cover gives an actual isomorphism of cover right modules. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory Opposite
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

noncomputable def cornerRecoveredModulePresheafIso
    (M : (E.cornerCoverZAlgebra Q).RightModule) :
    M.obj ≅ (E.cornerGradedRightModule Q M).recoveredRightModule.obj :=
  NatIso.ofComponents (fun X => (E.cornerAtObjectEquiv Q M X.unop).toModuleIso) (by
    intro X Y a
    apply ModuleCat.hom_ext
    exact E.cornerAtObjectEquiv_naturality Q M a)

noncomputable def cornerRecoveredModuleIso
    (M : (E.cornerCoverZAlgebra Q).RightModule) :
    M ≅ (E.cornerGradedRightModule Q M).recoveredRightModule where
  hom := (E.cornerRecoveredModulePresheafIso Q M).hom
  inv := (E.cornerRecoveredModulePresheafIso Q M).inv
  hom_inv_id := (E.cornerRecoveredModulePresheafIso Q M).hom_inv_id
  inv_hom_id := (E.cornerRecoveredModulePresheafIso Q M).inv_hom_id

end ASGinzburg.ZAlgebra.PeriodIso
