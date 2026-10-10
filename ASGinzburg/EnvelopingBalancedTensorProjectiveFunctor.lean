import ASGinzburg.EnvelopingBalancedTensorProjective
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves

/-! The genuine right-module-valued tensor functor preserves
projective objects. The size assumption is the ordinary module-category
comparison required by mathlib, with no algebraic restriction. -/
namespace ASGinzburg
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module Rᵐᵒᵖ M]
variable [IsScalarTower k Rᵐᵒᵖ M]

instance envelopingBalancedTensorRightFunctorPreservesProjectiveObjects
    [Small.{z} (AlgebraEnvelopingRing k R)] :
    (envelopingBalancedTensorRightFunctor.{u,v,w,z} k R M).PreservesProjectiveObjects where
  projective_obj {P} hP := by
    letI := hP
    letI := envelopingBalancedTensorRightModule k R M P
    haveI : Module.Projective Rᵐᵒᵖ (EnvelopingBalancedTensorSpace k R M P) :=
      envelopingBalancedTensor_projective k R M P
    exact ModuleCat.projective_of_categoryTheory_projective
      (ModuleCat.of Rᵐᵒᵖ (EnvelopingBalancedTensorSpace k R M P))

end ASGinzburg
