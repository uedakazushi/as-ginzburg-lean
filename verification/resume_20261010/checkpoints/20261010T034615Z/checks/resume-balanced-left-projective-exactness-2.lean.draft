import ASGinzburg.BalancedTensorProjectiveExactness
import ASGinzburg.BalancedTensorLeftAdjunction

/-! A genuine projective left module also makes balanced tensor exact
in the right-module variable. This is proved by the actual swap over the
opposite ring, including the double-opposite scalar transport. -/
namespace ASGinzburg
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (N : Type w) [AddCommGroup N] [Module k N] [Module R N]

attribute [local instance] RingHomInvPair.of_ringEquiv

noncomputable def balancedTensorDoubleOppositeScalarEquiv :
    letI := balancedTensorDoubleOppositeModule R N
    N ≃ₛₗ[(RingEquiv.opOp R : R →+* Rᵐᵒᵖᵐᵒᵖ)] N := by
  letI := balancedTensorDoubleOppositeModule R N
  exact
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem balancedTensorDoubleOppositeModule_projective [Module.Projective R N] :
    letI := balancedTensorDoubleOppositeModule R N
    Module.Projective Rᵐᵒᵖᵐᵒᵖ N := by
  letI := balancedTensorDoubleOppositeModule R N
  exact Module.Projective.of_ringEquiv (RingEquiv.opOp R)
    (balancedTensorDoubleOppositeScalarEquiv R N)

variable [IsScalarTower k R N] [Module.Projective R N]

instance balancedTensorLeftFunctorPreservesMonomorphisms :
    (balancedTensorLeftFunctor.{u,v,w,z} k R N).PreservesMonomorphisms := by
  letI := balancedTensorDoubleOppositeModule R N
  letI := balancedTensorDoubleOppositeIsScalarTower k R N
  letI := balancedTensorDoubleOppositeModule_projective R N
  letI := balancedTensorRightFunctorPreservesMonomorphisms.{u,v,w,z} k Rᵐᵒᵖ N
  exact Functor.preservesMonomorphisms.of_iso
    (balancedTensorLeftSwapIso.{u,v,w,z} k R N).symm

instance balancedTensorLeftFunctorPreservesHomology :
    (balancedTensorLeftFunctor.{u,v,w,max w z} k R N).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels _

theorem balancedTensorLeftFunctor_map_exact
    (S : ShortComplex (ModuleCat.{max w z} Rᵐᵒᵖ)) (hS : S.Exact) :
    (S.map (balancedTensorLeftFunctor.{u,v,w,max w z} k R N)).Exact :=
  hS.map _

end ASGinzburg
