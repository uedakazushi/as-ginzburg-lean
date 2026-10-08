import ASGinzburg.ExtComponentContravariance

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

theorem rightModuleExtPrecompLeft_zero {S : ShortComplex A.RightModule} (n : ℕ) :
    A.rightModuleExtPrecompLeft S.g n ≫ A.rightModuleExtPrecompLeft S.f n = 0 := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  ext e
  change (Abelian.Ext.mk₀ S.f).comp ((Abelian.Ext.mk₀ S.g).comp e (zero_add n)) (zero_add n) = 0
  rw [Abelian.Ext.mk₀_comp_mk₀_assoc, S.zero, Abelian.Ext.mk₀_zero, Abelian.Ext.zero_comp]

noncomputable def rightModuleExtLeftShortComplex (S : ShortComplex A.RightModule) (n : ℕ) :
    ShortComplex A.LeftModule :=
  ShortComplex.mk (A.rightModuleExtPrecompLeft S.g n) (A.rightModuleExtPrecompLeft S.f n)
    (A.rightModuleExtPrecompLeft_zero n)

theorem rightModuleExtLeftShortComplex_exact {S : ShortComplex A.RightModule}
    (hS : S.ShortExact) (n : ℕ) : (A.rightModuleExtLeftShortComplex S n).Exact := by
  apply (A.leftModule_exact_iff _).mpr
  intro i
  rw [ShortComplex.moduleCat_exact_iff]
  intro e he
  exact Abelian.Ext.contravariant_sequence_exact₂ hS (A.representable i) e he

theorem rightModuleExtLeftShortComplex_three_shortExact {S : ShortComplex A.RightModule}
    (hS : S.ShortExact)
    (h₂ : ∀ i, ∀ e : Abelian.Ext.{v} S.X₁ (A.representable i) 2, e = 0)
    (h₄ : ∀ i, ∀ e : Abelian.Ext.{v} S.X₃ (A.representable i) 4, e = 0) :
    (A.rightModuleExtLeftShortComplex S 3).ShortExact where
  exact := A.rightModuleExtLeftShortComplex_exact hS 3
  mono_f := by
    apply (A.leftModule_mono_iff _).mpr
    intro i
    apply (ModuleCat.mono_iff_injective _).mpr
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro e he
    obtain ⟨x,hx⟩ := Abelian.Ext.contravariant_sequence_exact₃ hS (A.representable i) e he
      (show 1+2=3 from rfl)
    rw [h₂ i x, Abelian.Ext.comp_zero] at hx
    exact hx.symm
  epi_g := by
    apply (A.leftModule_epi_iff _).mpr
    intro i
    apply (ModuleCat.epi_iff_surjective _).mpr
    intro e
    exact Abelian.Ext.contravariant_sequence_exact₁ hS (A.representable i) e
      (show 1+3=4 from rfl) (h₄ i _)
end ASGinzburg.ZAlgebra

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

theorem leftModuleExtPrecompRight_zero {S : ShortComplex A.LeftModule} (n : ℕ) :
    A.leftModuleExtPrecompRight S.g n ≫ A.leftModuleExtPrecompRight S.f n = 0 := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  ext e
  change (Abelian.Ext.mk₀ S.f).comp ((Abelian.Ext.mk₀ S.g).comp e (zero_add n)) (zero_add n) = 0
  rw [Abelian.Ext.mk₀_comp_mk₀_assoc, S.zero, Abelian.Ext.mk₀_zero, Abelian.Ext.zero_comp]

noncomputable def leftModuleExtRightShortComplex (S : ShortComplex A.LeftModule) (n : ℕ) :
    ShortComplex A.RightModule :=
  ShortComplex.mk (A.leftModuleExtPrecompRight S.g n) (A.leftModuleExtPrecompRight S.f n)
    (A.leftModuleExtPrecompRight_zero n)

theorem leftModuleExtRightShortComplex_exact {S : ShortComplex A.LeftModule}
    (hS : S.ShortExact) (n : ℕ) : (A.leftModuleExtRightShortComplex S n).Exact := by
  apply (A.rightModule_exact_iff _).mpr
  intro i
  rw [ShortComplex.moduleCat_exact_iff]
  intro e he
  exact Abelian.Ext.contravariant_sequence_exact₂ hS (A.leftRepresentable i) e he

theorem leftModuleExtRightShortComplex_three_shortExact {S : ShortComplex A.LeftModule}
    (hS : S.ShortExact)
    (h₂ : ∀ i, ∀ e : Abelian.Ext.{v} S.X₁ (A.leftRepresentable i) 2, e = 0)
    (h₄ : ∀ i, ∀ e : Abelian.Ext.{v} S.X₃ (A.leftRepresentable i) 4, e = 0) :
    (A.leftModuleExtRightShortComplex S 3).ShortExact where
  exact := A.leftModuleExtRightShortComplex_exact hS 3
  mono_f := by
    apply (A.rightModule_mono_iff _).mpr
    intro i
    apply (ModuleCat.mono_iff_injective _).mpr
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro e he
    obtain ⟨x,hx⟩ := Abelian.Ext.contravariant_sequence_exact₃ hS (A.leftRepresentable i) e he
      (show 1+2=3 from rfl)
    rw [h₂ i x, Abelian.Ext.comp_zero] at hx
    exact hx.symm
  epi_g := by
    apply (A.rightModule_epi_iff _).mpr
    intro i
    apply (ModuleCat.epi_iff_surjective _).mpr
    intro e
    exact Abelian.Ext.contravariant_sequence_exact₁ hS (A.leftRepresentable i) e
      (show 1+3=4 from rfl) (h₄ i _)
end ASGinzburg.ZAlgebra
