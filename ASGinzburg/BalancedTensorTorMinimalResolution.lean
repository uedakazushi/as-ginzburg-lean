import ASGinzburg.BalancedTensorTorLeft
import ASGinzburg.BalancedTensorMinimalComplex

/-! Tensoring a genuine projective resolution whose differential images
lie in an ideal action span with a module annihilated by that ideal computes
actual first-factor Tor by the tensor of each resolution term. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (N : Type w) [AddCommGroup N] [Module k N] [Module R N]

noncomputable def balancedTensorTorMinimalResolutionIso
    (M : ModuleCat.{max v w z} Rᵐᵒᵖ) (Q : ProjectiveResolution M)
    (I : Set R) (hN : ∀ r ∈ I, ∀ y : N, r • y = 0)
    (hQ : ∀ i j, ∀ x : Q.complex.X i, Q.complex.d i j x ∈ Submodule.span k
      {a : Q.complex.X j | ∃ r ∈ I, ∃ m : Q.complex.X j, MulOpposite.op r • m = a})
    (n : ℕ) :
    (balancedTensorTorLeftFunctor.{u,v,w,z} k R N n).obj M ≅
      (balancedTensorLeftFunctor.{u,v,w,max v w z} k R N).obj (Q.complex.X n) :=
  balancedTensorTorLeftResolutionIso k R N M Q n ≪≫
    balancedTensorMinimalComplexHomologyIso k R N Q.complex I hN hQ n

theorem balancedTensorTorMinimalResolution_isZero_iff
    (M : ModuleCat.{max v w z} Rᵐᵒᵖ) (Q : ProjectiveResolution M)
    (I : Set R) (hN : ∀ r ∈ I, ∀ y : N, r • y = 0)
    (hQ : ∀ i j, ∀ x : Q.complex.X i, Q.complex.d i j x ∈ Submodule.span k
      {a : Q.complex.X j | ∃ r ∈ I, ∃ m : Q.complex.X j, MulOpposite.op r • m = a})
    (n : ℕ) :
    IsZero ((balancedTensorTorLeftFunctor.{u,v,w,z} k R N n).obj M) ↔
      IsZero ((balancedTensorLeftFunctor.{u,v,w,max v w z} k R N).obj (Q.complex.X n)) :=
  (balancedTensorTorMinimalResolutionIso k R N M Q I hN hQ n).isZero_iff

end ASGinzburg
