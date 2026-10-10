import ASGinzburg.EnvelopingBalancedTensorRightMaps
import ASGinzburg.AlgebraEnvelopingRestrictionFunctor
import ASGinzburg.BalancedTensorRightFunctor

/-! Forgetting the residual right R action agrees with the actual
ordinary balanced tensor functor after left scalar restriction. -/
namespace ASGinzburg
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module Rᵐᵒᵖ M]

noncomputable def envelopingBalancedTensorForgetComponent
    (P : ModuleCat.{z} (AlgebraEnvelopingRing k R)) :
    ((envelopingBalancedTensorRightFunctor.{u,v,w,z} k R M) ⋙
      ModuleCat.restrictScalars (algebraMap k Rᵐᵒᵖ)).obj P ≅
    ((envelopingLeftRestrictionFunctor.{u,v,z} k R) ⋙
      balancedTensorRightFunctor.{u,v,w,z} k R M).obj P := by
  letI := envelopingLeftModule k R P
  letI := envelopingBalancedTensorRightModule k R M P
  letI := envelopingBalancedTensorRightScalarTower k R M P
  let e : ((envelopingBalancedTensorRightFunctor.{u,v,w,z} k R M) ⋙
      ModuleCat.restrictScalars (algebraMap k Rᵐᵒᵖ)).obj P ≃ₗ[k]
    ((envelopingLeftRestrictionFunctor.{u,v,z} k R) ⋙
      balancedTensorRightFunctor.{u,v,w,z} k R M).obj P := {
    toFun := id
    invFun := id
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun c t => by
      change (algebraMap k Rᵐᵒᵖ c) •
        (show EnvelopingBalancedTensorSpace k R M P from t)=c •
        (show EnvelopingBalancedTensorSpace k R M P from t)
      exact algebraMap_smul Rᵐᵒᵖ c (show EnvelopingBalancedTensorSpace k R M P from t)}
  exact e.toModuleIso

noncomputable def envelopingBalancedTensorForgetIso :
    (envelopingBalancedTensorRightFunctor.{u,v,w,z} k R M) ⋙
      ModuleCat.restrictScalars (algebraMap k Rᵐᵒᵖ) ≅
    (envelopingLeftRestrictionFunctor.{u,v,z} k R) ⋙
      balancedTensorRightFunctor.{u,v,w,z} k R M :=
  NatIso.ofComponents (envelopingBalancedTensorForgetComponent k R M) (by
    intro P P' f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    rfl)

end ASGinzburg
