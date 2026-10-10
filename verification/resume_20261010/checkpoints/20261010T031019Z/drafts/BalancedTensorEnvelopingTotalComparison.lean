import work.ASGinzburgDraft.BalancedTensorEnvelopingBicomplexComparison
import work.ASGinzburgDraft.BicomplexTotalFunctor
import work.ASGinzburgDraft.NatTotalExists

/-! Applying the actual enveloping balancing functor to the genuine
enveloping tensor total gives the ordinary balanced tensor total. The
isomorphism commutes with the actual finite diagonal coproducts and
signed differentials. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ModuleCat.Algebra
universe u v w
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (P : ChainComplex (ModuleCat.{max v w} Rᵐᵒᵖ) ℕ)
variable (Q : ChainComplex (ModuleCat.{max v w} R) ℕ)

attribute [local instance] regularEnvelopingModule regularEnvelopingScalarTower

noncomputable def balancedTensorEnvelopingTotalIso :
    ((balancedTensorLeftFunctor k (AlgebraEnvelopingRing k R) R).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
        (tensorRightEnvelopingTotal k R P Q (ComplexShape.down ℕ)) ≅
      mapBifunctor P Q (balancedTensorBifunctor k R) (ComplexShape.down ℕ) := by
  let G := balancedTensorLeftFunctor.{u,v,v,max v w} k (AlgebraEnvelopingRing k R) R
  let K := tensorRightEnvelopingBicomplex k R P Q
  letI : ∀ n, PreservesColimit
      (Discrete.functor (K.toGradedObject.mapObjFun
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)) n)) G :=
    fun _ => inferInstance
  exact bicomplexTotalFunctorIso G K (ComplexShape.down ℕ) ≪≫
    HomologicalComplex₂.total.mapIso
      (balancedTensorEnvelopingBicomplexIso k R P Q) (ComplexShape.down ℕ)

end ASGinzburg
