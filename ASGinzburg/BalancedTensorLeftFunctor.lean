import ASGinzburg.BalancedTensorLeftMaps
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-! Tensoring ordinary right R-modules with a fixed left R-module is an
actual additive k-linear functor on the module category. -/
namespace ASGinzburg
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (N : Type w) [AddCommGroup N] [Module k N] [Module R N]

noncomputable def balancedTensorLeftFunctor :
    ModuleCat.{z} Rᵐᵒᵖ ⥤ ModuleCat.{max w z} k where
  obj M := ModuleCat.of k (BalancedTensorSpace k R M N)
  map f := ModuleCat.ofHom (balancedTensorMapLeft k R N f.hom)
  map_id M := by
    apply ModuleCat.hom_ext
    apply balancedTensorSpace_linearMap_ext
    intro x y
    change balancedTensorMapLeft k R N (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M)
      (balancedTensorTmul k R M N x y) = balancedTensorTmul k R M N x y
    rw [balancedTensorMapLeft_tmul]
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply balancedTensorSpace_linearMap_ext
    intro x y
    change balancedTensorMapLeft k R N (g.hom.comp f.hom)
      (balancedTensorTmul k R _ N x y) =
        balancedTensorMapLeft k R N g.hom
          (balancedTensorMapLeft k R N f.hom (balancedTensorTmul k R _ N x y))
    rw [balancedTensorMapLeft_tmul, balancedTensorMapLeft_tmul,
      balancedTensorMapLeft_tmul]
    rfl

instance balancedTensorLeftFunctorAdditive :
    (balancedTensorLeftFunctor.{u,v,w,z} k R N).Additive where
  map_add := by
    intro M M' f g
    apply ModuleCat.hom_ext
    apply balancedTensorSpace_linearMap_ext
    intro x y
    change balancedTensorMapLeft k R N (f.hom + g.hom)
      (balancedTensorTmul k R M N x y) =
        balancedTensorMapLeft k R N f.hom (balancedTensorTmul k R M N x y) +
          balancedTensorMapLeft k R N g.hom (balancedTensorTmul k R M N x y)
    rw [balancedTensorMapLeft_tmul, balancedTensorMapLeft_tmul,
      balancedTensorMapLeft_tmul]
    exact congrArg (fun h => h y) ((balancedTensorBilinear k R M' N).map_add (f x) (g x))

instance balancedTensorLeftFunctorLinear :
    (balancedTensorLeftFunctor.{u,v,w,z} k R N).Linear k where
  map_smul := by
    intro M M' f c
    apply ModuleCat.hom_ext
    apply balancedTensorSpace_linearMap_ext
    intro x y
    change balancedTensorMapLeft k R N (c • f.hom)
      (balancedTensorTmul k R M N x y) =
        c • balancedTensorMapLeft k R N f.hom (balancedTensorTmul k R M N x y)
    rw [balancedTensorMapLeft_tmul, balancedTensorMapLeft_tmul]
    exact congrArg (fun h => h y) ((balancedTensorBilinear k R M' N).map_smul c (f x))

end ASGinzburg
