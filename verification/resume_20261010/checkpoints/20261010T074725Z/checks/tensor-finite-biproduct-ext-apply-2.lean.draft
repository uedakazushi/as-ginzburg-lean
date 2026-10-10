import work.ASGinzburgDraft.FiniteBiproductLinearExt

/-! Evaluation formulas for the genuine field-linear source-isomorphism
and finite-biproduct comparisons on actual Ext classes. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
universe u v w w₁ t
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable [HasDerivedCategory.{w₁} C] (k : Type t) [Field k] [Linear k C]
attribute [local instance] exactExtModule

theorem exactExtFiniteBiproductLinearEquiv_apply {J : Type*} [Fintype J]
    {X : J → C} {c : Bicone X} (hc : c.IsBilimit) (Y : C) (n : ℕ)
    (a : Abelian.Ext.{w} c.pt Y n) (i : J) :
    exactExtFiniteBiproductLinearEquiv k hc Y n a i =
      (Abelian.Ext.mk₀ (c.ι i)).comp a (zero_add n) := rfl

theorem exactExtSourceIsoLinearEquiv_symm_apply {X X' Y : C} (e : X ≅ X') (n : ℕ)
    (a : Abelian.Ext.{w} X Y n) :
    (exactExtSourceIsoLinearEquiv k (Y := Y) e n).symm a =
      (Abelian.Ext.mk₀ e.inv).comp a (zero_add n) := rfl

theorem exactExtFiniteBiproductSourceIsoFieldEquiv_apply {J : Type*} [Fintype J]
    {X : J → C} {c : Bicone X} (hc : c.IsBilimit) {S : C} (iso : S ≅ c.pt)
    (Y : C) (n : ℕ) (F : ∀ i, Abelian.Ext.{w} (X i) Y n ≃ₗ[k] k)
    (a : Abelian.Ext.{w} S Y n) (i : J) :
    (((exactExtSourceIsoLinearEquiv k (Y := Y) iso n).symm.trans
      (exactExtFiniteBiproductLinearEquiv k hc Y n)).trans
        (LinearEquiv.piCongrRight F)) a i =
      F i ((Abelian.Ext.mk₀ (c.ι i ≫ iso.inv)).comp a (zero_add n)) := by
  change F i ((Abelian.Ext.mk₀ (c.ι i)).comp
      ((Abelian.Ext.mk₀ iso.inv).comp a (zero_add n)) (zero_add n)) = _
  exact congrArg (F i) (Abelian.Ext.mk₀_comp_mk₀_assoc _ _ a)

end ASGinzburg
