import ASGinzburg.BalancedTensorLeftFunctor
import work.ASGinzburgDraft.AlgebraModuleRestrictionComparison

/-! The actual tensor functor uses the k-action obtained by restricting
an ordinary right module. Its tensor is canonically isomorphic to the
same balancing construction with any compatible original k-module action. -/
namespace ASGinzburg
open CategoryTheory
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k Rᵐᵒᵖ M]
variable (N : Type z) [AddCommGroup N] [Module k N] [Module R N]

noncomputable def balancedTensorScalarRestrictionMap :
    (balancedTensorLeftFunctor k R N).obj (ModuleCat.of Rᵐᵒᵖ M) ⟶
      ModuleCat.of k (BalancedTensorSpace k R M N) := by
  let e := algebraModuleRestrictScalarsIso k Rᵐᵒᵖ M
  let f := (balancedTensorBilinear k R M N).comp e.hom.hom
  exact ModuleCat.ofHom (balancedTensorLift k R
    ((ModuleCat.restrictScalars (algebraMap k Rᵐᵒᵖ)).obj (ModuleCat.of Rᵐᵒᵖ M)) N f (by
      intro r x y
      change balancedTensorTmul k R M N (MulOpposite.op r • (x : M)) y =
        balancedTensorTmul k R M N (x : M) (r • y)
      exact balancedTensorTmul_balance k R M N r x y))

noncomputable def balancedTensorScalarRestrictionInverse :
    ModuleCat.of k (BalancedTensorSpace k R M N) ⟶
      (balancedTensorLeftFunctor k R N).obj (ModuleCat.of Rᵐᵒᵖ M) := by
  let e := algebraModuleRestrictScalarsIso k Rᵐᵒᵖ M
  let T := (ModuleCat.restrictScalars (algebraMap k Rᵐᵒᵖ)).obj (ModuleCat.of Rᵐᵒᵖ M)
  let f := (balancedTensorBilinear k R T N).comp e.inv.hom
  exact ModuleCat.ofHom (balancedTensorLift k R M N f (by
    intro r x y
    change balancedTensorTmul k R T N (MulOpposite.op r • (x : T)) y =
      balancedTensorTmul k R T N (x : T) (r • y)
    exact balancedTensorTmul_balance k R T N r x y))

noncomputable def balancedTensorScalarRestrictionIso :
    (balancedTensorLeftFunctor k R N).obj (ModuleCat.of Rᵐᵒᵖ M) ≅
      ModuleCat.of k (BalancedTensorSpace k R M N) where
  hom := balancedTensorScalarRestrictionMap k R M N
  inv := balancedTensorScalarRestrictionInverse k R M N
  hom_inv_id := by
    apply ModuleCat.hom_ext
    let T := (ModuleCat.restrictScalars (algebraMap k Rᵐᵒᵖ)).obj (ModuleCat.of Rᵐᵒᵖ M)
    apply balancedTensorSpace_linearMap_ext k R T N
    intro x y
    change balancedTensorScalarRestrictionInverse k R M N
      (balancedTensorScalarRestrictionMap k R M N
        (balancedTensorTmul k R T N x y)) = balancedTensorTmul k R T N x y
    simp only [balancedTensorScalarRestrictionMap, balancedTensorScalarRestrictionInverse]
    rfl
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply balancedTensorSpace_linearMap_ext k R M N
    intro x y
    change balancedTensorScalarRestrictionMap k R M N
      (balancedTensorScalarRestrictionInverse k R M N
        (balancedTensorTmul k R M N x y)) = balancedTensorTmul k R M N x y
    simp only [balancedTensorScalarRestrictionMap, balancedTensorScalarRestrictionInverse]
    rfl

end ASGinzburg
