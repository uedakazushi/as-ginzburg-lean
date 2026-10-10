import ASGinzburg.BalancedTensorSpace
import Mathlib.Algebra.Category.ModuleCat.Basic

/-! Transporting equal field-module structures through the actual
balanced quotient also transports its pure tensors. -/
namespace ASGinzburg
open CategoryTheory
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R]
variable (M : Type w) [AddCommGroup M] [Module Rᵐᵒᵖ M]
variable (N : Type z) [AddCommGroup N] [Module k N] [Module R N]

noncomputable def balancedTensorFieldModuleChangeIso
    (P Q : Module k M) (h : P = Q) :
    ModuleCat.of k (@BalancedTensorSpace k _ R _ M _ P _ N _ _ _) ≅
      ModuleCat.of k (@BalancedTensorSpace k _ R _ M _ Q _ N _ _ _) := by
  cases h
  exact Iso.refl _

theorem balancedTensorFieldModuleChangeIso_hom_tmul
    (P Q : Module k M) (h : P = Q) (x : M) (y : N) :
    (balancedTensorFieldModuleChangeIso k R M N P Q h).hom
      (@balancedTensorTmul k _ R _ M _ P _ N _ _ _ x y) =
        @balancedTensorTmul k _ R _ M _ Q _ N _ _ _ x y := by
  cases h
  rfl

end ASGinzburg
