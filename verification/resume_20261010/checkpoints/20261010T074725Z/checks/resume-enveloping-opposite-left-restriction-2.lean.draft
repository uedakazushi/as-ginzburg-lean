import work.ASGinzburgDraft.AlgebraEnvelopingOppositeLeftProjective
import ASGinzburg.AlgebraEnvelopingRestrictionFunctor
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Exact

/-! The genuine right restriction functor along includeLeft.op is exact
and preserves projective objects over the actual enveloping algebra. -/
namespace ASGinzburg
open CategoryTheory
universe u v z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]

noncomputable abbrev envelopingOppositeLeftRestrictionFunctor :
    ModuleCat.{z} (AlgebraEnvelopingRing k R)ᵐᵒᵖ ⥤ ModuleCat.{z} Rᵐᵒᵖ :=
  ModuleCat.restrictScalars (AlgHom.op (Algebra.TensorProduct.includeLeft :
    R →ₐ[k] AlgebraEnvelopingRing k R)).toRingHom

instance envelopingOppositeLeftRestrictionFunctorPreservesProjectiveObjects
    [Small.{z} (AlgebraEnvelopingRing k R)ᵐᵒᵖ] :
    (envelopingOppositeLeftRestrictionFunctor.{u,v,z} k R).PreservesProjectiveObjects where
  projective_obj {P} hP := by
    letI := hP
    letI := envelopingOppositeLeftModule k R P
    haveI : Module.Projective Rᵐᵒᵖ P := envelopingOppositeLeftModule_projective k R P
    exact ModuleCat.projective_of_categoryTheory_projective (ModuleCat.of Rᵐᵒᵖ P)

instance envelopingOppositeLeftRestrictionFunctorPreservesHomology :
    (envelopingOppositeLeftRestrictionFunctor.{u,v,z} k R).PreservesHomology := by
  apply Functor.preservesHomology_of_map_exact
  intro C hC
  exact (ShortComplex.moduleCat_exact_iff _).mpr
    ((ShortComplex.moduleCat_exact_iff C).mp hC)

end ASGinzburg
