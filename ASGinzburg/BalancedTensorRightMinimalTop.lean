import ASGinzburg.BalancedTensorRightMinimalResolution
import ASGinzburg.BalancedTensorLeftQuotient
import ASGinzburg.OrdinaryIdealActionDirectSum
import Mathlib.RingTheory.Finiteness.Basic

/-! Actual second-factor Tor against the genuine right radical quotient
computes each actual minimal resolution term's radical top, including
its scalar-field finiteness and vanishing. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u v z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (J : Ideal R) [J.IsTwoSided]
variable (N : ModuleCat.{max v z} R) (P : ProjectiveResolution N)
variable (hP : ∀ i j, ∀ y : P.complex.X i,
  P.complex.d i j y ∈ ordinaryIdealActionSpan k R (P.complex.X j) J)

noncomputable def balancedTensorTorRightMinimalTopEquiv (n : ℕ) :
    (balancedTensorTorFunctor.{u,v,v,z} k R (R ⧸ J)ᵐᵒᵖ n).obj N ≃ₗ[k]
      ((P.complex.X n) ⧸ ordinaryIdealActionSpan k R (P.complex.X n) J) :=
  by
    let e₁ := balancedTensorTorRightMinimalResolutionIso.{u,v,v,z} k R (R ⧸ J)ᵐᵒᵖ N P
      (J : Set R) (idealQuotientRightModule_annihilated R J)
      (fun i j y => hP i j y) n
    let e₂ : BalancedTensorSpace k R (R ⧸ J)ᵐᵒᵖ (P.complex.X n) ≃ₗ[k]
        ((P.complex.X n) ⧸ ordinaryIdealActionSpan k R (P.complex.X n) J) :=
      balancedTensorLeftQuotientEquiv k R J (P.complex.X n)
    exact (e₁ ≪≫ e₂.toModuleIso).toLinearEquiv

noncomputable def balancedTensorTorRightMinimalTopIso (n : ℕ) :
    (balancedTensorTorFunctor.{u,v,v,z} k R (R ⧸ J)ᵐᵒᵖ n).obj N ≅
      ModuleCat.of k ((P.complex.X n) ⧸ ordinaryIdealActionSpan k R (P.complex.X n) J) :=
  (balancedTensorTorRightMinimalTopEquiv k R J N P hP n).toModuleIso

include hP in
theorem balancedTensorTorRightMinimalTop_finite (n : ℕ)
    [Module.Finite k ((balancedTensorTorFunctor.{u,v,v,z} k R (R ⧸ J)ᵐᵒᵖ n).obj N)] :
    Module.Finite k ((P.complex.X n) ⧸ ordinaryIdealActionSpan k R (P.complex.X n) J) :=
  Module.Finite.equiv (balancedTensorTorRightMinimalTopEquiv k R J N P hP n)

include hP in
theorem ordinaryIdealActionSpan_eq_top_of_minimal_tor_zero (n : ℕ)
    (hTor : IsZero ((balancedTensorTorFunctor.{u,v,v,z} k R (R ⧸ J)ᵐᵒᵖ n).obj N)) :
    ordinaryIdealActionSpan k R (P.complex.X n) J=⊤ := by
  let K := ordinaryIdealActionSpan k R (P.complex.X n) J
  have hQ : IsZero (ModuleCat.of k ((P.complex.X n) ⧸ K)) :=
    (balancedTensorTorRightMinimalTopIso k R J N P hP n).isZero_iff.mp hTor
  letI : Subsingleton ((P.complex.X n) ⧸ K) := ModuleCat.isZero_iff_subsingleton.mp hQ
  apply Submodule.eq_top_iff'.mpr
  intro x
  exact (Submodule.Quotient.mk_eq_zero K).mp (Subsingleton.elim _ _)

end ASGinzburg
