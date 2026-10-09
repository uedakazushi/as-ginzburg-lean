import ASGinzburg.PeriodCornerCoordinateMorphisms

/-! Actual module actions of homogeneous ring corners in vertex/sheet
coordinates. Composition is compatible with the original right-module action. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory Opposite
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

abbrev CornerModuleSpace (M : (E.cornerCoverZAlgebra Q).RightModule) (x : Q.LiftVertex) : Type v :=
  M.obj.obj (op (E.cornerCoordinateObject Q x))

abbrev CornerModuleTotalSpace (M : (E.cornerCoverZAlgebra Q).RightModule) :=
  ⨁ x : Q.LiftVertex,E.CornerModuleSpace Q M x

noncomputable def cornerModuleMap (M : (E.cornerCoverZAlgebra Q).RightModule)
    (x y : Q.LiftVertex) : E.CornerCoverHom Q x y →ₗ[k]
      (E.CornerModuleSpace Q M y →ₗ[k] E.CornerModuleSpace Q M x) where
  toFun f := (M.obj.map (E.cornerCoordinateHomEquiv Q x y f).op).hom
  map_add' := by
    intro f g
    letI := M.property.1
    rw [(E.cornerCoordinateHomEquiv Q x y).map_add]
    have h := M.obj.map_add (f:=(E.cornerCoordinateHomEquiv Q x y f).op)
      (g:=(E.cornerCoordinateHomEquiv Q x y g).op)
    simpa only [ModuleCat.hom_add] using congrArg (fun t => t.hom) h
  map_smul' := by
    intro c f
    letI := M.property.2
    rw [(E.cornerCoordinateHomEquiv Q x y).map_smul]
    have h := M.obj.map_smul c (E.cornerCoordinateHomEquiv Q x y f).op
    simpa only [ModuleCat.hom_smul] using congrArg (fun t => t.hom) h

theorem cornerModuleMap_comp (M : (E.cornerCoverZAlgebra Q).RightModule)
    {x y z : Q.LiftVertex} (f : E.CornerCoverHom Q x y) (g : E.CornerCoverHom Q y z) :
    (E.cornerModuleMap Q M x y f).comp (E.cornerModuleMap Q M y z g)=
      E.cornerModuleMap Q M x z (E.cornerCoverComp Q g f) := by
  change (M.obj.map (E.cornerCoordinateHomEquiv Q x y f).op).hom.comp
    (M.obj.map (E.cornerCoordinateHomEquiv Q y z g).op).hom=
      (M.obj.map (E.cornerCoordinateHomEquiv Q x z (E.cornerCoverComp Q g f)).op).hom
  have h := M.obj.map_comp (E.cornerCoordinateHomEquiv Q y z g).op
    (E.cornerCoordinateHomEquiv Q x y f).op
  rw [E.cornerCoordinateHomEquiv_comp]
  exact (congrArg (fun t => t.hom) h).symm

theorem cornerModuleMap_id (M : (E.cornerCoverZAlgebra Q).RightModule) (x : Q.LiftVertex) :
    E.cornerModuleMap Q M x x (E.cornerCoverId Q x)=
      LinearMap.id (R:=k) (M:=E.CornerModuleSpace Q M x) := by
  change (M.obj.map (E.cornerCoordinateHomEquiv Q x x (E.cornerCoverId Q x)).op).hom=_
  rw [E.cornerCoordinateHomEquiv_id]
  change (M.obj.map (𝟙 (op (E.cornerCoordinateObject Q x)))).hom=_
  rw [M.obj.map_id]
  rfl

end ASGinzburg.ZAlgebra.PeriodIso
