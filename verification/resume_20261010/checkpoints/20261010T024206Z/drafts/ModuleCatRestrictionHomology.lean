import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Exact

/-! Arbitrary scalar restriction of ordinary modules preserves
homology and reflects isomorphisms. -/
namespace ASGinzburg
open CategoryTheory
universe u v z
variable {R : Type u} [Ring R] {S : Type v} [Ring S] (f : R →+* S)

noncomputable def moduleCatRestrictionPreservesHomology :
    (ModuleCat.restrictScalars.{z} f).PreservesHomology := by
  apply Functor.preservesHomology_of_map_exact
  intro K hK
  exact (ShortComplex.moduleCat_exact_iff _).mpr
    ((ShortComplex.moduleCat_exact_iff K).mp hK)

def moduleCatRestrictionReflectsIsomorphisms :
    (ModuleCat.restrictScalars.{z} f).ReflectsIsomorphisms where
  reflects g _ := by
    have : IsIso ((forget (ModuleCat.{z} S)).map g) := by
      change IsIso ((forget (ModuleCat.{z} R)).map
        ((ModuleCat.restrictScalars f).map g))
      infer_instance
    exact isIso_of_reflects_iso g (forget (ModuleCat.{z} S))

end ASGinzburg
