import work.ASGinzburgDraft.ModuleCatULiftExactness
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! The actual field-vector universe-lift functor preserves homology. -/
namespace ASGinzburg
open CategoryTheory
universe u v w
variable (k : Type u) [Field k]

instance moduleCatULiftFunctorPreservesHomology :
    (moduleCatULiftFunctor.{u,v,w} k).PreservesHomology := by
  apply Functor.preservesHomology_of_map_exact
  intro S hS
  exact (moduleCatULiftFunctor_exact_iff k S).mpr hS

end ASGinzburg
