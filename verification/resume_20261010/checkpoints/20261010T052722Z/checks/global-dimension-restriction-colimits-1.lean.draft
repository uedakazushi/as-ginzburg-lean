import work.ASGinzburgDraft.ModuleCatRestrictionHomology

/-! Genuine scalar restriction preserves and reflects all colimits
whose indexing category lies in the ordinary module-carrier universe. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
universe u v z
variable {R : Type u} [Ring R] {S : Type v} [Ring S] (f : R →+* S)

noncomputable def moduleCatRestrictionPreservesSmallColimits :
    PreservesColimitsOfSize.{z,z} (ModuleCat.restrictScalars.{z} f) where
  preservesColimitsOfShape := {
    preservesColimit := fun {F} => by
      infer_instance }

noncomputable def moduleCatRestrictionReflectsSmallColimits :
    ReflectsColimitsOfSize.{z,z} (ModuleCat.restrictScalars.{z} f) := by
  letI := moduleCatRestrictionPreservesSmallColimits.{u,v,z} f
  letI := moduleCatRestrictionReflectsIsomorphisms.{u,v,z} f
  exact reflectsColimits_of_reflectsIsomorphisms

end ASGinzburg
