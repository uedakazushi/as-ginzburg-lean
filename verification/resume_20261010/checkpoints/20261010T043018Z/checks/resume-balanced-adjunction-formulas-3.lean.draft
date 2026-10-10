import ASGinzburg.BalancedTensorAdjunction

/-! The unit and counit of the genuine balanced tensor-Hom adjunction
are respectively the pure-tensor map and evaluation. -/
namespace ASGinzburg
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module Rᵐᵒᵖ M]
variable [IsScalarTower k Rᵐᵒᵖ M]

theorem balancedTensorAdjunction_unit_apply
    (N : ModuleCat.{max w z} R) (y : N) (x : M) :
    balancedTensorHomLinearEquiv k R M
      ((balancedTensorRightFunctor.{u,v,w,max w z} k R M).obj N)
      (((balancedTensorAdjunction.{u,v,w,z} k R M).unit.app N) y) x =
      balancedTensorTmul k R M N x y := rfl

theorem balancedTensorAdjunction_counit_tmul
    (P : ModuleCat.{max w z} k) (x : M)
    (f : BalancedTensorHom k R M P) :
    ((balancedTensorAdjunction.{u,v,w,z} k R M).counit.app P)
      (balancedTensorTmul k R M
        ((balancedTensorHomFunctor.{u,v,w,max w z} k R M).obj P) x f) = f x := by
  change balancedTensorUncurry k R M _ P LinearMap.id
    (balancedTensorTmul k R M _ x f) = f x
  rw [balancedTensorUncurry_tmul]
  rfl

end ASGinzburg
