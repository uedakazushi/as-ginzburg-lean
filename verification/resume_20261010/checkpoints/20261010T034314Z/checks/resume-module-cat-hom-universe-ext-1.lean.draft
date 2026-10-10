import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

/-! Ordinary modules over a ring in their own universe have actual Ext
in the Hom universe, from the genuine supply of projective modules. -/
namespace ASGinzburg
open CategoryTheory
universe v

instance moduleCatHomUniverseHasExt (R : Type v) [Ring R] :
    HasExt.{v} (ModuleCat.{v} R) :=
  hasExt_of_enoughProjectives (ModuleCat.{v} R)

end ASGinzburg
