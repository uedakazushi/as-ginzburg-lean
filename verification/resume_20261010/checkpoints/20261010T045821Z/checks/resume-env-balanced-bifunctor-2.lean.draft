import ASGinzburg.BalancedTensorRightFunctor
import ASGinzburg.BalancedTensorLeftFunctor
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! The actual noncommutative balancing quotient is additive in both
ordinary module variables. -/
namespace ASGinzburg
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]

noncomputable def balancedTensorBifunctor :
    ModuleCat.{w} Rᵐᵒᵖ ⥤ ModuleCat.{z} R ⥤ ModuleCat.{max w z} k where
  obj M := balancedTensorRightFunctor k R M
  map f :=
    { app N := ModuleCat.ofHom (balancedTensorMapLeft k R N f.hom)
      naturality {N N'} g := by
        apply ModuleCat.hom_ext
        apply balancedTensorSpace_linearMap_ext
        intro m n
        change balancedTensorMapLeft k R N' f.hom
            (balancedTensorMapRight k R _ g.hom (balancedTensorTmul k R _ _ m n)) =
          balancedTensorMapRight k R _ g.hom
            (balancedTensorMapLeft k R N f.hom (balancedTensorTmul k R _ _ m n))
        rw [balancedTensorMapRight_tmul, balancedTensorMapLeft_tmul,
          balancedTensorMapLeft_tmul, balancedTensorMapRight_tmul] }
  map_id M := by
    apply NatTrans.ext
    funext N
    exact (balancedTensorLeftFunctor k R N).map_id M
  map_comp f g := by
    apply NatTrans.ext
    funext N
    exact (balancedTensorLeftFunctor k R N).map_comp f g

instance balancedTensorBifunctor_obj_additive (M : ModuleCat.{w} Rᵐᵒᵖ) :
    ((balancedTensorBifunctor.{u,v,w,z} k R).obj M).Additive :=
  balancedTensorRightFunctorAdditive k R M

instance balancedTensorBifunctor_additive :
    (balancedTensorBifunctor.{u,v,w,z} k R).Additive where
  map_add {X Y f g} := by
    apply NatTrans.ext
    funext N
    exact (balancedTensorLeftFunctor k R N).map_add (f := f) (g := g)

theorem balancedTensorBifunctor_map_app_tmul
    {M M' : ModuleCat.{w} Rᵐᵒᵖ} (f : M ⟶ M') (N : ModuleCat.{z} R)
    (m : M) (n : N) :
    ((balancedTensorBifunctor k R).map f).app N (balancedTensorTmul k R M N m n) =
      balancedTensorTmul k R M' N (f m) n :=
  balancedTensorMapLeft_tmul k R N f.hom m n

theorem balancedTensorBifunctor_obj_map_tmul
    (M : ModuleCat.{w} Rᵐᵒᵖ) {N N' : ModuleCat.{z} R} (g : N ⟶ N')
    (m : M) (n : N) :
    ((balancedTensorBifunctor k R).obj M).map g (balancedTensorTmul k R M N m n) =
      balancedTensorTmul k R M N' m (g n) :=
  balancedTensorMapRight_tmul k R M g.hom m n

end ASGinzburg
