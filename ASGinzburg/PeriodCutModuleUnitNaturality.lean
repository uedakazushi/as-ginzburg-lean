import ASGinzburg.PeriodCutModuleComparisonValues
import ASGinzburg.PeriodCutCornerTotalActions
import ASGinzburg.PeriodCutGradedFunctorFaithful

/-! The original-to-recovered component equivalences are natural in all cover morphisms. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory Opposite
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

theorem cornerAtObjectEquiv_naturality
    (M : (E.cornerCoverZAlgebra Q).RightModule)
    {X Y : (E.cornerCoverZAlgebra Q).Objᵒᵖ} (a : X⟶Y) :
    (E.cornerAtObjectEquiv Q M Y.unop).toLinearMap.comp (M.obj.map a).hom=
      ((E.cornerGradedRightModule Q M).recoveredRightModule.obj.map a).hom.comp
        (E.cornerAtObjectEquiv Q M X.unop).toLinearMap := by
  cases X using Opposite.rec
  cases Y using Opposite.rec
  rename_i X Y
  obtain ⟨y,rfl⟩ := E.cornerCoordinateObject_surjective Q X
  obtain ⟨x,rfl⟩ := E.cornerCoordinateObject_surjective Q Y
  obtain ⟨b,hb⟩ := (E.cornerCoordinateHomEquiv Q x y).surjective a.unop
  have ha : a=(E.cornerCoordinateHomEquiv Q x y b).op := Quiver.Hom.unop_inj hb.symm
  subst a
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change (E.cornerAtObjectEquiv Q M (E.cornerCoordinateObject Q x)
    ((M.obj.map (E.cornerCoordinateHomEquiv Q x y b).op).hom v)).val=
    (E.cutRightRepresentation Q M (E.cornerCoordinateHomEquiv Q x y b).val).unop
      (E.cornerAtObjectEquiv Q M (E.cornerCoordinateObject Q y) v).val
  rw [E.cornerAtObjectEquiv_coordinate_val,E.cornerAtObjectEquiv_coordinate_val,
    E.cornerCoordinateHomEquiv_val]
  exact (E.cutRightRepresentation_corner_lof Q M b v).symm

end ASGinzburg.ZAlgebra.PeriodIso
