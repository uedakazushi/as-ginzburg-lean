import ASGinzburg.PeriodCutRecoveredModuleUnitIso

/-! The original-to-recovered cover-module isomorphism is natural in the module. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory Opposite
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

noncomputable def cornerRecoveredUnitNaturalIso :
    𝟭 (E.cornerCoverZAlgebra Q).RightModule ≅
      E.cornerGradedModuleFunctor Q ⋙ CutGradedRightModule.recoveredModuleFunctor (E:=E) :=
  NatIso.ofComponents (E.cornerRecoveredModuleIso Q) (by
    intro M N f
    apply NatTrans.ext
    funext X
    cases X using Opposite.rec
    rename_i X
    obtain ⟨x,rfl⟩ := E.cornerCoordinateObject_surjective Q X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change (E.cornerAtObjectEquiv Q N (E.cornerCoordinateObject Q x)
      ((f.app (op (E.cornerCoordinateObject Q x))).hom v)).val=
      E.cornerTotalModuleLinearMap Q f
        (E.cornerAtObjectEquiv Q M (E.cornerCoordinateObject Q x) v).val
    rw [E.cornerAtObjectEquiv_coordinate_val,E.cornerAtObjectEquiv_coordinate_val,
      E.cornerTotalModuleLinearMap_lof])

end ASGinzburg.ZAlgebra.PeriodIso
