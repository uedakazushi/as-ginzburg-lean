import work.ASGinzburgDraft.BalancedTensorEnvelopingTorComparison
import work.ASGinzburgDraft.BalancedTensorTorBalanceConsequences
import work.ASGinzburgDraft.BalancedTensorLeftFieldModuleChange

/-! Genuine second-factor enveloping Tor compared with first-factor
ordinary Tor. The fixed regular module's induced field action is
transported explicitly before using the actual enveloping comparison. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u v
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable {M : ModuleCat.{v} Rᵐᵒᵖ} {N : ModuleCat.{v} R}
variable (P : ProjectiveResolution M) (Q : ProjectiveResolution N)

attribute [local instance] regularEnvelopingModule regularEnvelopingScalarTower

set_option maxHeartbeats 800000 in
noncomputable def balancedTensorEnvelopingSecondTorComparisonIso (n : ℕ) :
    (balancedTensorTorFunctor.{u,v,v,v} k (AlgebraEnvelopingRing k R)
      (((tensorRightEnvelopingBifunctor k R).obj M).obj N) n).obj
        (ModuleCat.of (AlgebraEnvelopingRing k R) R) ≅
      (balancedTensorTorLeftFunctor.{u,v,v,v} k R N n).obj M :=
  (balancedTensorTorBalanceObjIso k (AlgebraEnvelopingRing k R)
    (((tensorRightEnvelopingBifunctor k R).obj M).obj N)
    (ModuleCat.of (AlgebraEnvelopingRing k R) R) n).symm ≪≫
  (balancedTensorTorLeftCanonicalFieldIso k (AlgebraEnvelopingRing k R) R n).app
    (((tensorRightEnvelopingBifunctor k R).obj M).obj N) ≪≫
  balancedTensorEnvelopingTorComparisonIso k R P Q n

include Q in
theorem balancedTensorEnvelopingSecondTor_isZero_of_resolution_term
    (n : ℕ) (hP : IsZero (P.complex.X n)) :
    IsZero ((balancedTensorTorFunctor.{u,v,v,v} k (AlgebraEnvelopingRing k R)
      (((tensorRightEnvelopingBifunctor k R).obj M).obj N) n).obj
        (ModuleCat.of (AlgebraEnvelopingRing k R) R)) :=
  IsZero.of_iso (balancedTensorTorLeft_isZero_of_resolution_term k R N M P n hP)
    (balancedTensorEnvelopingSecondTorComparisonIso k R P Q n)

include Q in
set_option maxHeartbeats 800000 in
theorem balancedTensorEnvelopingSecondTor_finite_of_resolution_term
    (n : ℕ) [Module.Finite Rᵐᵒᵖ (P.complex.X n)] [Module.Finite k N] :
    Module.Finite k ((balancedTensorTorFunctor.{u,v,v,v} k (AlgebraEnvelopingRing k R)
      (((tensorRightEnvelopingBifunctor k R).obj M).obj N) n).obj
        (ModuleCat.of (AlgebraEnvelopingRing k R) R)) := by
  haveI : Module.Finite k ((balancedTensorTorLeftFunctor.{u,v,v,v} k R N n).obj M) :=
    balancedTensorTorLeft_finite_of_resolution_term.{u,v,v,v} k R N M P n
  let e := balancedTensorEnvelopingSecondTorComparisonIso k R P Q n
  exact Module.Finite.equiv e.toLinearEquiv.symm

end ASGinzburg
