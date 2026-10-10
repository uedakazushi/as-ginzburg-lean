import Mathlib.Algebra.Homology.BifunctorHomotopy

/-! Total complexes of additive bifunctors preserve genuine homotopy
equivalences in their first variable. This is a concrete bridge for
contracting underlying vector-space tensor resolutions. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Category HomologicalComplex
variable {C₁ C₂ D I₁ I₂ J : Type*}
variable [Category C₁] [Category C₂] [Category D]
variable [Preadditive C₁] [Preadditive C₂] [Preadditive D]
variable {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
variable (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
variable (c : ComplexShape J) [DecidableEq J] [TotalComplexShape c₁ c₂ c]

theorem bifunctorTotalMap_id
    (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂)
    [HasMapBifunctor K₁ K₂ F c] :
    mapBifunctorMap (𝟙 K₁) (𝟙 K₂) F c = 𝟙 (mapBifunctor K₁ K₂ F c) := by
  simp [mapBifunctorMap]

theorem bifunctorTotalMap_comp
    {K₁ L₁ M₁ : HomologicalComplex C₁ c₁}
    {K₂ L₂ M₂ : HomologicalComplex C₂ c₂}
    [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c] [HasMapBifunctor M₁ M₂ F c]
    (f₁ : K₁ ⟶ L₁) (g₁ : L₁ ⟶ M₁) (f₂ : K₂ ⟶ L₂) (g₂ : L₂ ⟶ M₂) :
    mapBifunctorMap f₁ f₂ F c ≫ mapBifunctorMap g₁ g₂ F c =
      mapBifunctorMap (f₁ ≫ g₁) (f₂ ≫ g₂) F c := by
  unfold mapBifunctorMap
  rw [← HomologicalComplex₂.total.map_comp]
  congr 1
  simp only [Functor.map_comp, NatTrans.comp_app, assoc]
  rw [NatTrans.naturality_assoc]

noncomputable def bifunctorTotalHomotopyEquivLeft
    {K₁ L₁ : HomologicalComplex C₁ c₁} (h : HomotopyEquiv K₁ L₁)
    (K₂ : HomologicalComplex C₂ c₂)
    [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ K₂ F c] :
    HomotopyEquiv (mapBifunctor K₁ K₂ F c) (mapBifunctor L₁ K₂ F c) where
  hom := mapBifunctorMap h.hom (𝟙 K₂) F c
  inv := mapBifunctorMap h.inv (𝟙 K₂) F c
  homotopyHomInvId := by
    have hh := mapBifunctorMapHomotopy₁ h.homotopyHomInvId (𝟙 K₂) F c
    simpa only [bifunctorTotalMap_comp, id_comp, bifunctorTotalMap_id] using hh
  homotopyInvHomId := by
    have hh := mapBifunctorMapHomotopy₁ h.homotopyInvHomId (𝟙 K₂) F c
    simpa only [bifunctorTotalMap_comp, id_comp, bifunctorTotalMap_id] using hh

end ASGinzburg
