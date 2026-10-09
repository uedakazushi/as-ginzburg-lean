import ASGinzburg.PeriodCornerModuleMaps

/-! Genuine finite-support total-space operators for native ring corners.
Connected composition agrees with R multiplication and disconnected
composition is zero. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory Opposite
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

noncomputable def cornerTotalEntryMap (M : (E.cornerCoverZAlgebra Q).RightModule)
    (x y : Q.LiftVertex) : E.CornerCoverHom Q x y →ₗ[k]
      Module.End k (E.CornerModuleTotalSpace Q M) where
  toFun f := (DirectSum.lof k Q.LiftVertex (E.CornerModuleSpace Q M) x).comp
    ((E.cornerModuleMap Q M x y f).comp
      (DirectSum.component k Q.LiftVertex (E.CornerModuleSpace Q M) y))
  map_add' := by intro f g;rw [map_add,LinearMap.add_comp,LinearMap.comp_add]
  map_smul' := by
    intro c f
    rw [map_smul,LinearMap.smul_comp,LinearMap.comp_smul,RingHom.id_apply]

theorem cornerTotalEntryMap_lof (M : (E.cornerCoverZAlgebra Q).RightModule)
    (x y : Q.LiftVertex) (f : E.CornerCoverHom Q x y) (v : E.CornerModuleSpace Q M y) :
    E.cornerTotalEntryMap Q M x y f
      (DirectSum.lof k Q.LiftVertex (E.CornerModuleSpace Q M) y v)=
        DirectSum.lof k Q.LiftVertex (E.CornerModuleSpace Q M) x
          (E.cornerModuleMap Q M x y f v) := by
  simp [cornerTotalEntryMap]

theorem cornerTotalEntryMap_lof_ne (M : (E.cornerCoverZAlgebra Q).RightModule)
    (x y t : Q.LiftVertex) (f : E.CornerCoverHom Q x y)
    (v : E.CornerModuleSpace Q M t) (h : t≠y) :
    E.cornerTotalEntryMap Q M x y f
      (DirectSum.lof k Q.LiftVertex (E.CornerModuleSpace Q M) t v)=0 := by
  simp [cornerTotalEntryMap,DirectSum.component.of,h]

theorem cornerTotalEntryMap_comp (M : (E.cornerCoverZAlgebra Q).RightModule)
    {x y z : Q.LiftVertex} (f : E.CornerCoverHom Q x y) (g : E.CornerCoverHom Q y z) :
    (E.cornerTotalEntryMap Q M x y f).comp (E.cornerTotalEntryMap Q M y z g)=
      E.cornerTotalEntryMap Q M x z (E.cornerCoverComp Q g f) := by
  apply DFinsupp.lhom_ext
  intro t v
  change E.cornerTotalEntryMap Q M x y f
    (E.cornerTotalEntryMap Q M y z g (DirectSum.lof k Q.LiftVertex _ t v))=
      E.cornerTotalEntryMap Q M x z (E.cornerCoverComp Q g f) (DirectSum.lof k Q.LiftVertex _ t v)
  by_cases ht : t=z
  · subst t
    rw [E.cornerTotalEntryMap_lof,E.cornerTotalEntryMap_lof,E.cornerTotalEntryMap_lof]
    exact congrArg (DirectSum.lof k Q.LiftVertex _ x)
      (LinearMap.congr_fun (E.cornerModuleMap_comp Q M f g) v)
  · rw [E.cornerTotalEntryMap_lof_ne Q M y z t g v ht,map_zero,
      E.cornerTotalEntryMap_lof_ne Q M x z t (E.cornerCoverComp Q g f) v ht]

theorem cornerTotalEntryMap_comp_ne (M : (E.cornerCoverZAlgebra Q).RightModule)
    {x y z w : Q.LiftVertex} (f : E.CornerCoverHom Q x y) (g : E.CornerCoverHom Q z w)
    (h : z≠y) :
    (E.cornerTotalEntryMap Q M x y f).comp (E.cornerTotalEntryMap Q M z w g)=0 := by
  apply DFinsupp.lhom_ext
  intro t v
  change E.cornerTotalEntryMap Q M x y f
    (E.cornerTotalEntryMap Q M z w g (DirectSum.lof k Q.LiftVertex _ t v))=0
  by_cases ht : t=w
  · subst t
    rw [E.cornerTotalEntryMap_lof,E.cornerTotalEntryMap_lof_ne Q M x y z f _ h]
  · rw [E.cornerTotalEntryMap_lof_ne Q M z w t g v ht,map_zero]

end ASGinzburg.ZAlgebra.PeriodIso
