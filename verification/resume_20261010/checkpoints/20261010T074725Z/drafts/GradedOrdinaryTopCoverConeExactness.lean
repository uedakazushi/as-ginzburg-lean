import work.ASGinzburgDraft.GradedOrdinaryTopCoverConeMaps

/-! Exactness of the actual top-cover cone at its two middle terms
implies exactness of the original four-term complex at the corresponding terms. -/
namespace ASGinzburg.GradedOrdinaryModuleData
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]
variable {A : ℤ → Submodule k R}
variable (P₀ P₁ P₂ P₃ V : GradedOrdinaryModuleData k R A)

theorem exact_of_topCoverConeIncoming_exact
    (f₀ : P₀.ringModule ⟶ P₁.ringModule) (f₁ : P₁.ringModule ⟶ P₂.ringModule)
    (h : f₀ ≫ f₁ = 0)
    (he : (ShortComplex.mk f₀ (P₁.topCoverConeIncoming P₂ V f₁)
      (P₀.comp_topCoverConeIncoming P₁ P₂ V f₀ f₁ h)).Exact) :
    (ShortComplex.mk f₀ f₁ h).Exact := by
  rw [ShortComplex.moduleCat_exact_iff] at he ⊢
  intro x hx
  apply he x
  change (f₁ x, (0 : V.ringModule)) = 0
  exact Prod.ext hx rfl

theorem exact_of_topCoverConeOutgoing_exact
    (f₁ : P₁.ringModule ⟶ P₂.ringModule) (f₂ : P₂.ringModule ⟶ P₃.ringModule)
    (l : V.ringModule ⟶ P₃.ringModule) (h : f₁ ≫ f₂ = 0)
    (he : (ShortComplex.mk (P₁.topCoverConeIncoming P₂ V f₁)
      (P₂.topCoverConeOutgoing P₃ V f₂ l)
      (P₁.topCoverConeIncoming_comp_outgoing P₂ P₃ V f₁ f₂ l h)).Exact) :
    (ShortComplex.mk f₁ f₂ h).Exact := by
  rw [ShortComplex.moduleCat_exact_iff] at he ⊢
  intro x hx
  have hz : (P₂.topCoverConeOutgoing P₃ V f₂ l).hom (x, 0) = 0 := by
    change f₂ x + l 0 = 0
    rw [map_zero, add_zero]
    exact hx
  obtain ⟨y, hy⟩ := he (x, 0) hz
  exact ⟨y, congrArg Prod.fst hy⟩

end ASGinzburg.GradedOrdinaryModuleData
