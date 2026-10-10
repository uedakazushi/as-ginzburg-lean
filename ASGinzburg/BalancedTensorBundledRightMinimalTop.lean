import ASGinzburg.IdealQuotientRightFieldComparison
import ASGinzburg.BalancedTensorRightMinimalTop

/-! The actual bundled right ideal quotient computes the actual radical
top of each genuine minimal left projective-resolution term. -/
namespace ASGinzburg
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (J : Ideal R) [J.IsTwoSided]
variable (N : ModuleCat.{max v z} R) (P : ProjectiveResolution N)
variable (hP : ∀ i j, ∀ y : P.complex.X i,
  P.complex.d i j y ∈ ordinaryIdealActionSpan k R (P.complex.X j) J)

noncomputable def balancedTensorTorBundledRightMinimalTopEquiv (n : ℕ) :
    (balancedTensorTorFunctor.{u,v,v,z} k R (idealQuotientRightObject J) n).obj N ≃ₗ[k]
      ((P.complex.X n) ⧸ ordinaryIdealActionSpan k R (P.complex.X n) J) := by
  let e₀ :
      (balancedTensorTorFunctor.{u,v,v,z} k R (idealQuotientRightObject J) n).obj N ≅
        (balancedTensorTorFunctor.{u,v,v,z} k R (R ⧸ J)ᵐᵒᵖ n).obj N :=
    (balancedTensorTorIdealQuotientCanonicalFieldIso.{u,v,z} k R J n).app N
  let e₁ :
      (balancedTensorTorFunctor.{u,v,v,z} k R (R ⧸ J)ᵐᵒᵖ n).obj N ≃ₗ[k]
        ((P.complex.X n) ⧸ ordinaryIdealActionSpan k R (P.complex.X n) J) :=
    balancedTensorTorRightMinimalTopEquiv.{u,v,z} k R J N P hP n
  exact e₀.toLinearEquiv.trans e₁

end ASGinzburg
