import work.ASGinzburgDraft.GradedOrdinaryTopCoverConeMaps

/-! An actual isomorphism on the reduced top cokernel makes the cone
of its lifted projective cover surjective and exact in degree two. -/
namespace ASGinzburg.GradedOrdinaryModuleData
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u v w
variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]
variable {A : ℤ → Submodule k R}
variable (P₁ P₂ P₃ V : GradedOrdinaryModuleData k R A)
variable {S : Type w} [Ring S]
variable (F : ModuleCat.{v} R ⥤ ModuleCat.{w} S) [F.Additive]

theorem topCoverConeFunctor_exact_one (P₀ : GradedOrdinaryModuleData k R A)
    (f₀ : P₀.ringModule ⟶ P₁.ringModule) (f₁ : P₁.ringModule ⟶ P₂.ringModule)
    (h₀ : f₀ ≫ f₁ = 0) (hF₀ : ((ShortComplex.mk f₀ f₁ h₀).map F).Exact) :
    ((ShortComplex.mk f₀ (P₁.topCoverConeIncoming P₂ V f₁)
      (P₀.comp_topCoverConeIncoming P₁ P₂ V f₀ f₁ h₀)).map F).Exact := by
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro x hx
  change F.map (P₁.topCoverConeIncoming P₂ V f₁) x = 0 at hx
  have hz : F.map f₁ x = 0 := by
    have h := congrArg (fun y => F.map (P₂.binaryProductFst V) y) hx
    dsimp only at h
    rw [map_zero] at h
    change (F.map (P₁.topCoverConeIncoming P₂ V f₁) ≫
      F.map (P₂.binaryProductFst V)) x = 0 at h
    rw [← F.map_comp,P₁.topCoverConeIncoming_comp_fst P₂ V] at h
    exact h
  obtain ⟨z,hz⟩ := (ShortComplex.moduleCat_exact_iff _).mp hF₀ x hz
  exact ⟨z,hz⟩

theorem topCoverConeFunctor_outgoing_epi
    (f₂ : P₂.ringModule ⟶ P₃.ringModule) (l : V.ringModule ⟶ P₃.ringModule)
    {U : ModuleCat.{v} R} (q : P₃.ringModule ⟶ U) (hq : f₂ ≫ q = 0)
    (hF : ((ShortComplex.mk f₂ q hq).map F).Exact)
    [Epi (F.map q)] [IsIso (F.map (l ≫ q))] :
    Epi (F.map (P₂.topCoverConeOutgoing P₃ V f₂ l)) := by
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro y
  have hπ : Function.Surjective (F.map (l ≫ q)) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨z,hz⟩ := hπ (F.map q y)
  have hd : F.map q (y - F.map l z) = 0 := by
    rw [map_sub]
    change F.map q y - (F.map l ≫ F.map q) z = 0
    rw [← F.map_comp,hz,sub_self]
  obtain ⟨x,hx⟩ := (ShortComplex.moduleCat_exact_iff _).mp hF (y - F.map l z) hd
  change F.map f₂ x = y - F.map l z at hx
  refine ⟨F.map (P₂.binaryProductInl V) x + F.map (P₂.binaryProductInr V) z,?_⟩
  rw [map_add]
  have hi : F.map (P₂.topCoverConeOutgoing P₃ V f₂ l)
      (F.map (P₂.binaryProductInl V) x) = F.map f₂ x := by
    change (F.map (P₂.binaryProductInl V) ≫
      F.map (P₂.topCoverConeOutgoing P₃ V f₂ l)) x = _
    rw [← F.map_comp,P₂.binaryProductInl_comp_topCoverConeOutgoing P₃ V]
  have hj : F.map (P₂.topCoverConeOutgoing P₃ V f₂ l)
      (F.map (P₂.binaryProductInr V) z) = F.map l z := by
    change (F.map (P₂.binaryProductInr V) ≫
      F.map (P₂.topCoverConeOutgoing P₃ V f₂ l)) z = _
    rw [← F.map_comp,P₂.binaryProductInr_comp_topCoverConeOutgoing P₃ V]
  rw [hi,hj,hx,sub_add_cancel]

theorem topCoverConeFunctor_exact_two
    (f₁ : P₁.ringModule ⟶ P₂.ringModule) (f₂ : P₂.ringModule ⟶ P₃.ringModule)
    (l : V.ringModule ⟶ P₃.ringModule) (h₁ : f₁ ≫ f₂ = 0)
    (hF₁ : ((ShortComplex.mk f₁ f₂ h₁).map F).Exact)
    {U : ModuleCat.{v} R} (q : P₃.ringModule ⟶ U) (hq : f₂ ≫ q = 0)
    [IsIso (F.map (l ≫ q))] :
    ((ShortComplex.mk (P₁.topCoverConeIncoming P₂ V f₁)
      (P₂.topCoverConeOutgoing P₃ V f₂ l)
      (P₁.topCoverConeIncoming_comp_outgoing P₂ P₃ V f₁ f₂ l h₁)).map F).Exact := by
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro y hy
  change F.map (P₂.topCoverConeOutgoing P₃ V f₂ l) y = 0 at hy
  have hπ : Function.Injective (F.map (l ≫ q)) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hs : F.map (P₂.binaryProductSnd V) y = 0 := by
    apply hπ
    rw [map_zero]
    change (F.map (P₂.binaryProductSnd V) ≫ F.map (l ≫ q)) y = 0
    rw [← F.map_comp,← P₂.topCoverConeOutgoing_comp_topProjection P₃ V f₂ l q hq,
      F.map_comp]
    change F.map q (F.map (P₂.topCoverConeOutgoing P₃ V f₂ l) y) = 0
    rw [hy,map_zero]
  have hc := P₂.binaryProductFunctor_coordinates V F y
  rw [hs,map_zero,add_zero] at hc
  have hi (x : F.obj P₂.ringModule) :
      F.map (P₂.topCoverConeOutgoing P₃ V f₂ l)
        (F.map (P₂.binaryProductInl V) x) = F.map f₂ x := by
    change (F.map (P₂.binaryProductInl V) ≫
      F.map (P₂.topCoverConeOutgoing P₃ V f₂ l)) x = _
    rw [← F.map_comp,P₂.binaryProductInl_comp_topCoverConeOutgoing P₃ V]
  have hcy : F.map f₂ (F.map (P₂.binaryProductFst V) y) = 0 := by
    rw [← hi,hc,hy]
  obtain ⟨z,hz⟩ := (ShortComplex.moduleCat_exact_iff _).mp hF₁
    (F.map (P₂.binaryProductFst V) y) hcy
  change F.map f₁ z = F.map (P₂.binaryProductFst V) y at hz
  refine ⟨z,?_⟩
  change F.map (f₁ ≫ P₂.binaryProductInl V) z = y
  rw [F.map_comp]
  change F.map (P₂.binaryProductInl V) (F.map f₁ z) = y
  rw [hz,hc]

end ASGinzburg.GradedOrdinaryModuleData
