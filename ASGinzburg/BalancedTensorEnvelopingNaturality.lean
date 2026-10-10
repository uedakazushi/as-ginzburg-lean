import ASGinzburg.BalancedTensorEnvelopingComparison
import ASGinzburg.AlgebraEnvelopingTensorRightMaps
import ASGinzburg.BalancedTensorLeftMaps
import ASGinzburg.BalancedTensorRightMaps

/-! Naturality of the genuine enveloping balanced tensor comparison
in both tensor factors. Tensor products of module maps are genuinely
right-enveloping-linear before they are passed to the balancing quotient. -/
namespace ASGinzburg
open scoped TensorProduct
universe u v w w' z z'
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable {M : Type w} [AddCommGroup M] [Module k M] [Module Rᵐᵒᵖ M]
variable {M' : Type w'} [AddCommGroup M'] [Module k M'] [Module Rᵐᵒᵖ M']
variable {N : Type z} [AddCommGroup N] [Module k N] [Module R N]
variable {N' : Type z'} [AddCommGroup N'] [Module k N'] [Module R N']
variable [IsScalarTower k Rᵐᵒᵖ M] [IsScalarTower k Rᵐᵒᵖ M']
variable [IsScalarTower k R N] [IsScalarTower k R N']

attribute [local instance] tensorRightEnvelopingModule regularEnvelopingModule
  tensorRightEnvelopingScalarTower

theorem balancedTensorEnvelopingComparisonMap_naturality
    (f : M →ₗ[Rᵐᵒᵖ] M') (g : N →ₗ[R] N') :
    (balancedTensorEnvelopingComparisonMap k R M' N').comp
      (balancedTensorMapLeft k (AlgebraEnvelopingRing k R) R
        (tensorRightEnvelopingMap k R f g)) =
      (balancedTensorMapLeft k R N' f).comp
        ((balancedTensorMapRight k R M g).comp
          (balancedTensorEnvelopingComparisonMap k R M N)) := by
  apply balancedTensorSpace_linearMap_ext k (AlgebraEnvelopingRing k R) (M ⊗[k] N) R
  intro x r
  have h :
      ((balancedTensorEnvelopingComparisonMap k R M' N').comp
        (balancedTensorMapLeft k (AlgebraEnvelopingRing k R) R
          (tensorRightEnvelopingMap k R f g))).comp
        ((balancedTensorBilinear k (AlgebraEnvelopingRing k R) (M ⊗[k] N) R).flip r) =
      ((balancedTensorMapLeft k R N' f).comp
        ((balancedTensorMapRight k R M g).comp
          (balancedTensorEnvelopingComparisonMap k R M N))).comp
        ((balancedTensorBilinear k (AlgebraEnvelopingRing k R) (M ⊗[k] N) R).flip r) := by
    apply TensorProduct.ext'
    intro m n
    change balancedTensorEnvelopingComparisonMap k R M' N'
      (balancedTensorMapLeft k (AlgebraEnvelopingRing k R) R
        (tensorRightEnvelopingMap k R f g)
        (balancedTensorTmul k (AlgebraEnvelopingRing k R) (M ⊗[k] N) R (m ⊗ₜ[k] n) r)) =
      balancedTensorMapLeft k R N' f
        (balancedTensorMapRight k R M g
          (balancedTensorEnvelopingComparisonMap k R M N
            (balancedTensorTmul k (AlgebraEnvelopingRing k R) (M ⊗[k] N) R (m ⊗ₜ[k] n) r)))
    rw [balancedTensorMapLeft_tmul, tensorRightEnvelopingMap_tmul,
      balancedTensorEnvelopingComparisonMap_tmul, balancedTensorEnvelopingComparisonMap_tmul,
      balancedTensorMapRight_tmul, balancedTensorMapLeft_tmul, g.map_smul]
  exact DFunLike.congr_fun h x

theorem balancedTensorEnvelopingComparisonInverse_naturality
    (f : M →ₗ[Rᵐᵒᵖ] M') (g : N →ₗ[R] N') :
    (balancedTensorMapLeft k (AlgebraEnvelopingRing k R) R
      (tensorRightEnvelopingMap k R f g)).comp
      (balancedTensorEnvelopingComparisonInverse k R M N) =
      (balancedTensorEnvelopingComparisonInverse k R M' N').comp
        ((balancedTensorMapLeft k R N' f).comp (balancedTensorMapRight k R M g)) := by
  apply balancedTensorSpace_linearMap_ext k R M N
  intro m n
  simp only [LinearMap.comp_apply, balancedTensorEnvelopingComparisonInverse_tmul,
    balancedTensorMapLeft_tmul, tensorRightEnvelopingMap_tmul, balancedTensorMapRight_tmul]

end ASGinzburg
