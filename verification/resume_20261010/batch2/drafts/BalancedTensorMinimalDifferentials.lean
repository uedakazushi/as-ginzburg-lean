import ASGinzburg.BalancedTensorTorMinimalResolution

/-! The genuine ideal-action image condition on ordinary differentials,
with ModuleCat's scalar action fixed explicitly by its algebra structure. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]

def BalancedTensorMinimalDifferentials
    (C : ChainComplex (ModuleCat.{z} Rᵐᵒᵖ) ℕ) (I : Set R) : Prop :=
  ∀ i j, ∀ x : C.X i, C.d i j x ∈ Submodule.span k
    {a : C.X j | ∃ r ∈ I, ∃ m : C.X j, MulOpposite.op r • m = a}

variable (N : Type w) [AddCommGroup N] [Module k N] [Module R N]

theorem balancedTensorTorMinimalDifferentials_isZero_iff
    (M : ModuleCat.{max v w z} Rᵐᵒᵖ) (P : ProjectiveResolution M)
    (I : Set R) (hN : ∀ r ∈ I, ∀ y : N, r • y = 0)
    (hP : BalancedTensorMinimalDifferentials k R P.complex I) (n : ℕ) :
    IsZero ((balancedTensorTorLeftFunctor.{u,v,w,z} k R N n).obj M) ↔
      IsZero ((balancedTensorLeftFunctor.{u,v,w,max v w z} k R N).obj (P.complex.X n)) :=
  balancedTensorTorMinimalResolution_isZero_iff k R N M P I hN hP n

end ASGinzburg
