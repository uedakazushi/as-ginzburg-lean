import ASGinzburg.BalancedTensorRightMapLaws
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-! The concrete noncommutative balanced tensor quotient gives an
actual additive and k-linear functor on the ordinary R-module category. -/
namespace ASGinzburg
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module Rᵐᵒᵖ M]

noncomputable def balancedTensorRightFunctor : ModuleCat.{z} R ⥤ ModuleCat.{max w z} k where
  obj N := ModuleCat.of k (BalancedTensorSpace k R M N)
  map g := ModuleCat.ofHom (balancedTensorMapRight k R M g.hom)
  map_id N := by
    apply ModuleCat.hom_ext
    exact balancedTensorMapRight_id k R M
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact balancedTensorMapRight_comp k R M f.hom g.hom

instance balancedTensorRightFunctorAdditive :
    (balancedTensorRightFunctor.{u,v,w,z} k R M).Additive where
  map_add := by
    intro N N' f g
    apply ModuleCat.hom_ext
    exact balancedTensorMapRight_add k R M f.hom g.hom

instance balancedTensorRightFunctorLinear :
    (balancedTensorRightFunctor.{u,v,w,z} k R M).Linear k where
  map_smul := by
    intro N N' g c
    apply ModuleCat.hom_ext
    exact balancedTensorMapRight_smul k R M c g.hom

end ASGinzburg
