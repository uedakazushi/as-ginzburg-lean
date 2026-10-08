import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C]

theorem mappingCone_descShortComplex_natural
    {S T : ShortComplex (CochainComplex C ℤ)} (φ : S ⟶ T) :
    CochainComplex.mappingCone.map S.f T.f φ.τ₁ φ.τ₂ φ.comm₁₂.symm ≫
        CochainComplex.mappingCone.descShortComplex T =
      CochainComplex.mappingCone.descShortComplex S ≫ φ.τ₃ := by
  ext n
  simp only [HomologicalComplex.comp_f]
  rw [CochainComplex.mappingCone.ext_from_iff _ (n+1) n rfl]
  constructor
  · simp [CochainComplex.mappingCone.map,CochainComplex.mappingCone.descShortComplex]
  · simpa [CochainComplex.mappingCone.map,CochainComplex.mappingCone.descShortComplex]
      using HomologicalComplex.congr_hom φ.comm₂₃ n

variable [HasDerivedCategory.{w} C]

theorem triangleOfSESδ_natural
    {S T : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) :
    DerivedCategory.Q.map φ.τ₃ ≫ DerivedCategory.triangleOfSESδ hT =
      DerivedCategory.triangleOfSESδ hS ≫ (DerivedCategory.Q.map φ.τ₁)⟦(1 : ℤ)⟧' := by
  let α := CochainComplex.mappingCone.map S.f T.f φ.τ₁ φ.τ₂ φ.comm₁₂.symm
  haveI := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  haveI := CochainComplex.mappingCone.quasiIso_descShortComplex hT
  have Hq : DerivedCategory.Q.map φ.τ₃ ≫
      inv (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex T)) =
    inv (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S)) ≫
      DerivedCategory.Q.map α := by
    rw [IsIso.comp_inv_eq,Category.assoc,IsIso.eq_inv_comp]
    simp only [← Functor.map_comp]
    exact congrArg DerivedCategory.Q.map (mappingCone_descShortComplex_natural φ).symm
  have Hδ := (DerivedCategory.Q.mapTriangle.map
    (CochainComplex.mappingCone.triangleMap S.f T.f φ.τ₁ φ.τ₂ φ.comm₁₂.symm)).comm₃
  change (DerivedCategory.Q.map (CochainComplex.mappingCone.triangle S.f).mor₃ ≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app S.X₁) ≫
      (DerivedCategory.Q.map φ.τ₁)⟦(1 : ℤ)⟧' =
    DerivedCategory.Q.map α ≫ DerivedCategory.Q.map (CochainComplex.mappingCone.triangle T.f).mor₃ ≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app T.X₁ at Hδ
  simp only [Category.assoc] at Hδ
  dsimp [DerivedCategory.triangleOfSESδ]
  rw [← Category.assoc,← Category.assoc,Hq]
  simp only [Category.assoc]
  exact congrArg (fun f =>
    inv (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S)) ≫ f) Hδ.symm
theorem singleδ_natural {S T : ShortComplex C} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) :
    (DerivedCategory.singleFunctor C 0).map φ.τ₃ ≫ hT.singleδ =
      hS.singleδ ≫ ((DerivedCategory.singleFunctor C 0).map φ.τ₁)⟦(1 : ℤ)⟧' := by
  let e := (SingleFunctors.evaluation _ _ 0).mapIso (DerivedCategory.singleFunctorsPostcompQIso C)
  let F := HomologicalComplex.single C (ComplexShape.up ℤ) 0
  let ψ : S.map F ⟶ T.map F := F.mapShortComplex.map φ
  have Hδ := triangleOfSESδ_natural (hS.map_of_exact F) (hT.map_of_exact F) ψ
  change DerivedCategory.Q.map (F.map φ.τ₃) ≫
      DerivedCategory.triangleOfSESδ (hT.map_of_exact F) =
    DerivedCategory.triangleOfSESδ (hS.map_of_exact F) ≫
      (DerivedCategory.Q.map (F.map φ.τ₁))⟦(1 : ℤ)⟧' at Hδ
  change (DerivedCategory.singleFunctor C 0).map φ.τ₃ ≫ e.hom.app T.X₃ ≫
      DerivedCategory.triangleOfSESδ (hT.map_of_exact F) ≫ (e.inv.app T.X₁)⟦(1 : ℤ)⟧' =
    (e.hom.app S.X₃ ≫ DerivedCategory.triangleOfSESδ (hS.map_of_exact F) ≫
      (e.inv.app S.X₁)⟦(1 : ℤ)⟧') ≫
        ((DerivedCategory.singleFunctor C 0).map φ.τ₁)⟦(1 : ℤ)⟧'
  have H₃ := e.hom.naturality φ.τ₃
  change (DerivedCategory.singleFunctor C 0).map φ.τ₃ ≫ e.hom.app T.X₃ =
    e.hom.app S.X₃ ≫ DerivedCategory.Q.map (F.map φ.τ₃) at H₃
  have H₁ := e.inv.naturality φ.τ₁
  change DerivedCategory.Q.map (F.map φ.τ₁) ≫ e.inv.app T.X₁ =
    e.inv.app S.X₁ ≫ (DerivedCategory.singleFunctor C 0).map φ.τ₁ at H₁
  rw [← Category.assoc,← Category.assoc,H₃]
  simp only [Category.assoc]
  change e.hom.app S.X₃ ≫ DerivedCategory.Q.map (F.map φ.τ₃) ≫
      DerivedCategory.triangleOfSESδ (hT.map_of_exact F) ≫ (e.inv.app T.X₁)⟦(1 : ℤ)⟧' = _
  rw [← Category.assoc (DerivedCategory.Q.map (F.map φ.τ₃)),Hδ]
  simp only [Category.assoc]
  congr 2
  rw [← Functor.map_comp,H₁,Functor.map_comp]
end ASGinzburg

namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
universe u v t
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{t} C]

theorem extClass_natural {S T : ShortComplex C} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) :
    hS.extClass.comp (Abelian.Ext.mk₀ φ.τ₁) (Nat.add_zero 1) =
      (Abelian.Ext.mk₀ φ.τ₃).comp hT.extClass (Nat.zero_add 1) := by
  letI := HasDerivedCategory.standard C
  ext
  simp only [Abelian.Ext.comp_hom,Abelian.Ext.mk₀_hom,
    ShortComplex.ShortExact.extClass_hom,ShiftedHom.comp_mk₀,ShiftedHom.mk₀_comp]
  exact (singleδ_natural hS hT φ).symm

theorem extBoundary_natural {S T : ShortComplex C} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) (N : C) (n : ℕ) (e : Abelian.Ext.{t} T.X₁ N n) :
    hS.extClass.comp ((Abelian.Ext.mk₀ φ.τ₁).comp e (Nat.zero_add n)) (Nat.add_comm 1 n) =
      (Abelian.Ext.mk₀ φ.τ₃).comp (hT.extClass.comp e (Nat.add_comm 1 n)) (Nat.zero_add (n+1)) := by
  rw [← Abelian.Ext.comp_assoc_of_second_deg_zero,extClass_natural hS hT φ]
  apply Abelian.Ext.comp_assoc
  omega
end ASGinzburg
