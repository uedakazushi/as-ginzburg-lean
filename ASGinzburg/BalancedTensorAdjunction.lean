import ASGinzburg.BalancedTensorHomFunctor
import Mathlib.CategoryTheory.Adjunction.Basic

/-! The genuine tensor-Hom adjunction for ordinary modules over an
arbitrary noncommutative k-algebra. All maps use the balancing quotient
and the source right R-action, rather than an additional duality assumption. -/
namespace ASGinzburg
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module Rᵐᵒᵖ M]
variable [IsScalarTower k Rᵐᵒᵖ M]

noncomputable def balancedTensorModuleHomEquiv
    (N : ModuleCat.{max w z} R) (P : ModuleCat.{max w z} k) :
    ((balancedTensorRightFunctor k R M).obj N ⟶ P) ≃
      (N ⟶ (balancedTensorHomFunctor k R M).obj P) where
  toFun f := ModuleCat.ofHom (balancedTensorCurry k R M N P f.hom)
  invFun g := ModuleCat.ofHom (balancedTensorUncurry k R M N P g.hom)
  left_inv f := by
    apply ModuleCat.hom_ext
    exact (balancedTensorHomEquiv k R M N P).left_inv f.hom
  right_inv g := by
    apply ModuleCat.hom_ext
    exact (balancedTensorHomEquiv k R M N P).right_inv g.hom

noncomputable def balancedTensorAdjunction :
    balancedTensorRightFunctor.{u,v,w,max w z} k R M ⊣
      balancedTensorHomFunctor.{u,v,w,max w z} k R M :=
  Adjunction.mkOfHomEquiv
    { homEquiv := balancedTensorModuleHomEquiv k R M
      homEquiv_naturality_left_symm := by
        intro N' N P f g
        apply ModuleCat.hom_ext
        exact balancedTensorUncurry_naturality_source k R M f.hom g.hom
      homEquiv_naturality_right := by
        intro N P P' f g
        apply ModuleCat.hom_ext
        exact balancedTensorCurry_naturality_target k R M f.hom g.hom }

instance balancedTensorRightFunctorIsLeftAdjoint :
    (balancedTensorRightFunctor.{u,v,w,max w z} k R M).IsLeftAdjoint :=
  (balancedTensorAdjunction.{u,v,w,z} k R M).isLeftAdjoint

end ASGinzburg
