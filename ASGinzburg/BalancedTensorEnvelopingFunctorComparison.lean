import ASGinzburg.BalancedTensorBifunctor
import ASGinzburg.AlgebraEnvelopingTensorBifunctor
import ASGinzburg.BalancedTensorEnvelopingNaturality
import ASGinzburg.BalancedTensorLeftAdjunction
import ASGinzburg.AlgebraEnvelopingScalars
import ASGinzburg.BalancedTensorFieldModuleChange

/-! The concrete enveloping balancing equivalence on bundled module
objects, including the change from their induced field action to the
canonical field action on the tensor product. -/
namespace ASGinzburg
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u v w z
set_option maxHeartbeats 200000
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : ModuleCat.{max v w} Rᵐᵒᵖ) (N : ModuleCat.{max v z} R)

attribute [local instance] tensorRightEnvelopingModule tensorRightEnvelopingScalarTower
  regularEnvelopingModule regularEnvelopingScalarTower

theorem tensorRightEnvelopingBifunctor_moduleOfAlgebraModule_eq :
    (Module.compHom (((tensorRightEnvelopingBifunctor k R).obj M).obj N)
      (algebraMap k (AlgebraEnvelopingRing k R)ᵐᵒᵖ) : Module k (M ⊗[k] N)) =
      (inferInstance : Module k (M ⊗[k] N)) := by
  apply Module.ext'
  intro c x
  change tensorRightEnvelopingRepresentation k R M N
    (algebraMap k (AlgebraEnvelopingRing k R)ᵐᵒᵖ c) x =
      c • (show M ⊗[k] N from x)
  rw [AlgHom.commutes]
  rfl

noncomputable def balancedTensorEnvelopingTensorScalarIso :
    (balancedTensorLeftFunctor k (AlgebraEnvelopingRing k R) R).obj
        (((tensorRightEnvelopingBifunctor k R).obj M).obj N) ≅
      ModuleCat.of k (BalancedTensorSpace k (AlgebraEnvelopingRing k R) (M ⊗[k] N) R) :=
  balancedTensorFieldModuleChangeIso k (AlgebraEnvelopingRing k R) (M ⊗[k] N) R
    (Module.compHom (((tensorRightEnvelopingBifunctor k R).obj M).obj N)
      (algebraMap k (AlgebraEnvelopingRing k R)ᵐᵒᵖ)) inferInstance
    (tensorRightEnvelopingBifunctor_moduleOfAlgebraModule_eq k R M N)

theorem balancedTensorEnvelopingTensorScalarIso_hom_tmul (x : M ⊗[k] N) (r : R) :
    (balancedTensorEnvelopingTensorScalarIso k R M N).hom
      (@balancedTensorTmul k _ (AlgebraEnvelopingRing k R) _
        (((tensorRightEnvelopingBifunctor k R).obj M).obj N) _
        (Module.compHom (((tensorRightEnvelopingBifunctor k R).obj M).obj N)
          (algebraMap k (AlgebraEnvelopingRing k R)ᵐᵒᵖ)) _ R _ _ _ x r) =
      balancedTensorTmul k (AlgebraEnvelopingRing k R) (M ⊗[k] N) R x r :=
  balancedTensorFieldModuleChangeIso_hom_tmul k (AlgebraEnvelopingRing k R)
    (M ⊗[k] N) R _ _ (tensorRightEnvelopingBifunctor_moduleOfAlgebraModule_eq k R M N) x r

noncomputable def balancedTensorEnvelopingModuleIso :
    (balancedTensorLeftFunctor k (AlgebraEnvelopingRing k R) R).obj
        (((tensorRightEnvelopingBifunctor k R).obj M).obj N) ≅
      (((balancedTensorBifunctor k R).obj M).obj N) :=
  balancedTensorEnvelopingTensorScalarIso k R M N ≪≫
    (balancedTensorEnvelopingComparisonEquiv k R M N).toModuleIso

theorem balancedTensorEnvelopingModuleIso_hom_tmul (m : M) (n : N) (r : R) :
    (balancedTensorEnvelopingModuleIso k R M N).hom
      (@balancedTensorTmul k _ (AlgebraEnvelopingRing k R) _
        (((tensorRightEnvelopingBifunctor k R).obj M).obj N) _
        (Module.compHom (((tensorRightEnvelopingBifunctor k R).obj M).obj N)
          (algebraMap k (AlgebraEnvelopingRing k R)ᵐᵒᵖ)) _ R _ _ _ (m ⊗ₜ[k] n) r) =
      balancedTensorTmul k R M N m (r • n) := by
  change balancedTensorEnvelopingComparisonMap k R M N
    ((balancedTensorEnvelopingTensorScalarIso k R M N).hom _) = _
  rw [balancedTensorEnvelopingTensorScalarIso_hom_tmul,
    balancedTensorEnvelopingComparisonMap_tmul]

end ASGinzburg
