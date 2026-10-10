import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Algebra.Tower

/-! Restricting an algebra-module scalar action recovers any given
compatible original k-module by the actual identity on its elements. -/
namespace ASGinzburg
open CategoryTheory
universe u v w
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module R M]
  [IsScalarTower k R M]

noncomputable def algebraModuleRestrictScalarsIso :
    (ModuleCat.restrictScalars (algebraMap k R)).obj (ModuleCat.of R M) ≅
      ModuleCat.of k M := by
  have h : ∀ (c : k) (x : M), (algebraMap k R c) • x = c • x :=
    fun c x => algebraMap_smul R c x
  exact LinearEquiv.toModuleIso <|
    @AddEquiv.toLinearEquiv _ _ _ _ _ _
      (((ModuleCat.restrictScalars (algebraMap k R)).obj (ModuleCat.of R M)).isModule) _
      (AddEquiv.refl M) (fun c x => h c x)

@[simp] theorem algebraModuleRestrictScalarsIso_hom_apply
    (x : (ModuleCat.restrictScalars (algebraMap k R)).obj (ModuleCat.of R M)) :
    (algebraModuleRestrictScalarsIso k R M).hom x = x := rfl

@[simp] theorem algebraModuleRestrictScalarsIso_inv_apply (x : M) :
    (algebraModuleRestrictScalarsIso k R M).inv x = x := rfl

end ASGinzburg
