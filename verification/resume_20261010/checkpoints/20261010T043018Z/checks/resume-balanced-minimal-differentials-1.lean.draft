import ASGinzburg.BalancedTensorMinimalComplex

/-! The genuine ideal-action image condition on ordinary differentials,
with ModuleCat's scalar action fixed explicitly by its algebra structure. -/
namespace ASGinzburg
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]

def BalancedTensorMinimalDifferentials
    (C : ChainComplex (ModuleCat.{z} Rᵐᵒᵖ) ℕ) (I : Set R) : Prop :=
  ∀ i j, ∀ x : C.X i, C.d i j x ∈ Submodule.span k
    {a : C.X j | ∃ r ∈ I, ∃ m : C.X j, MulOpposite.op r • m = a}

end ASGinzburg
