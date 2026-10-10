import work.ASGinzburgDraft.PeriodCutCornerFieldTotal

/-! The actual field total-space functor is naturally the exact discrete
colimit of component evaluations, with canonical insertion compatibility. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

@[reassoc] theorem cornerFieldTotalObjIso_ι_hom
    (M : (E.cornerCoverZAlgebra Q).RightModule) (x : Q.LiftVertex) :
    colimit.ι ((E.cornerFieldComponents Q).obj M) (Discrete.mk x) ≫
      (E.cornerFieldTotalObjIso Q M).hom=
        ModuleCat.ofHom (DirectSum.lof k Q.LiftVertex (E.CornerModuleSpace Q M) x) := by
  simp [cornerFieldTotalObjIso]

noncomputable def cornerFieldTotalNatIso : E.cornerFieldTotalFunctor Q ≅ E.cornerTotalSpaceFunctor Q :=
  NatIso.ofComponents (E.cornerFieldTotalObjIso Q) (by
    intro M N f
    apply colimit.hom_ext
    intro x
    change colimit.ι ((E.cornerFieldComponents Q).obj M) x ≫
        (colimMap ((E.cornerFieldComponents Q).map f) ≫ (E.cornerFieldTotalObjIso Q N).hom)=
      colimit.ι ((E.cornerFieldComponents Q).obj M) x ≫
        ((E.cornerFieldTotalObjIso Q M).hom ≫ ModuleCat.ofHom (E.cornerTotalModuleLinearMap Q f))
    rw [← Category.assoc,ι_colimMap,Category.assoc,E.cornerFieldTotalObjIso_ι_hom]
    rw [← Category.assoc,E.cornerFieldTotalObjIso_ι_hom]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    exact (E.cornerTotalModuleLinearMap_lof Q f x.as y).symm)

noncomputable instance cornerTotalSpaceFunctorPreservesFiniteLimits :
    PreservesFiniteLimits (E.cornerTotalSpaceFunctor Q) :=
  preservesFiniteLimits_of_natIso (E.cornerFieldTotalNatIso Q)

noncomputable instance cornerTotalSpaceFunctorPreservesFiniteColimits :
    PreservesFiniteColimits (E.cornerTotalSpaceFunctor Q) :=
  preservesFiniteColimits_of_natIso (E.cornerFieldTotalNatIso Q)

end ASGinzburg.ZAlgebra.PeriodIso
