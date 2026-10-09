import ASGinzburg.PeriodCornerTotalEntryMaps

/-! Corner action followed by insertion into the total space is intrinsic:
equal source vertices and equal ring values give the same insertion map. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory Opposite
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

noncomputable def cornerInsertionMap (M : (E.cornerCoverZAlgebra Q).RightModule)
    (x y : Q.LiftVertex) : E.CornerCoverHom Q x y →ₗ[k]
      (E.CornerModuleSpace Q M y →ₗ[k] E.CornerModuleTotalSpace Q M) where
  toFun f := (DirectSum.lof k Q.LiftVertex (E.CornerModuleSpace Q M) x).comp
    (E.cornerModuleMap Q M x y f)
  map_add' := by intro f g;rw [map_add,LinearMap.comp_add]
  map_smul' := by intro c f;rw [map_smul,LinearMap.comp_smul,RingHom.id_apply]

theorem cornerInsertionMap_congr_source (M : (E.cornerCoverZAlgebra Q).RightModule)
    (x x' y : Q.LiftVertex) (h : x=x')
    (f : E.CornerCoverHom Q x y) (f' : E.CornerCoverHom Q x' y) (hf : f.val=f'.val) :
    E.cornerInsertionMap Q M x y f=E.cornerInsertionMap Q M x' y f' := by
  subst x'
  have he : f=f' := Subtype.ext hf
  rw [he]

theorem cornerInsertionMap_comp (M : (E.cornerCoverZAlgebra Q).RightModule)
    {x y z : Q.LiftVertex} (f : E.CornerCoverHom Q x y) (g : E.CornerCoverHom Q y z) :
    E.cornerInsertionMap Q M x z (E.cornerCoverComp Q g f)=
      (E.cornerInsertionMap Q M x y f).comp (E.cornerModuleMap Q M y z g) := by
  change (DirectSum.lof k Q.LiftVertex _ x).comp
    (E.cornerModuleMap Q M x z (E.cornerCoverComp Q g f))=
      ((DirectSum.lof k Q.LiftVertex _ x).comp (E.cornerModuleMap Q M x y f)).comp
        (E.cornerModuleMap Q M y z g)
  rw [← E.cornerModuleMap_comp,LinearMap.comp_assoc]

theorem cornerTotalEntryMap_insertion (M : (E.cornerCoverZAlgebra Q).RightModule)
    {x y : Q.LiftVertex} (f : E.CornerCoverHom Q x y) :
    E.cornerTotalEntryMap Q M x y f=
      (E.cornerInsertionMap Q M x y f).comp
        (DirectSum.component k Q.LiftVertex (E.CornerModuleSpace Q M) y) := by
  change (DirectSum.lof k Q.LiftVertex _ x).comp
    ((E.cornerModuleMap Q M x y f).comp (DirectSum.component k Q.LiftVertex _ y))=_
  rw [← LinearMap.comp_assoc]
  rfl

end ASGinzburg.ZAlgebra.PeriodIso
