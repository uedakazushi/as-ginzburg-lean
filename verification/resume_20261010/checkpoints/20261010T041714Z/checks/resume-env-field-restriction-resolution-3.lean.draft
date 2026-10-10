import ASGinzburg.MapProjectiveResolutionOfTerms
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Every genuine algebra-module projective resolution restricts to a
genuine vector-space projective resolution: scalar restriction is exact
and every vector space is free. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
universe u v w
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]

theorem moduleCatField_projective (M : ModuleCat.{w} k) : Projective M := by
  letI : Module.Projective k M := inferInstance
  exact ModuleCat.projective_of_categoryTheory_projective M

noncomputable instance moduleFieldRestrictionPreservesHomology :
    (ModuleCat.restrictScalars.{w} (algebraMap k R)).PreservesHomology := by
  let G := ModuleCat.restrictScalars.{w} (algebraMap k R)
  letI : ∀ {X Y : ModuleCat.{w} R} (f : X ⟶ Y),
      PreservesColimit (parallelPair f 0) G := fun _ => inferInstance
  exact Functor.preservesHomology_of_preservesMonos_and_cokernels G

noncomputable def moduleFieldRestrictionResolution {M : ModuleCat.{w} R}
    (P : ProjectiveResolution M) :
    ProjectiveResolution ((ModuleCat.restrictScalars (algebraMap k R)).obj M) :=
  mapProjectiveResolutionOfTerms (ModuleCat.restrictScalars (algebraMap k R)) P
    (fun _ => moduleCatField_projective k _)

end ASGinzburg
