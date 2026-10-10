import ASGinzburg.BifunctorTotalResolution

/-! The degree-zero canonical augmentation of the tensor total of two
resolutions agrees with the tensor of their genuine augmentations. -/
namespace ASGinzburg
open CategoryTheory HomologicalComplex
variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]
variable [Abelian C₁] [Abelian C₂] [Preadditive D] [CategoryTheory.Limits.HasZeroObject D]
variable (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
variable {M : C₁} {N : C₂} [Projective M] [Projective N]
variable (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
variable [HasMapBifunctor P.complex Q.complex F (ComplexShape.down ℕ)]

theorem bifunctorTotalResolutionHomotopyEquiv_ι_zero :
    ιMapBifunctor P.complex Q.complex F (ComplexShape.down ℕ) 0 0 0 (by simp) ≫
        (bifunctorTotalResolutionHomotopyEquiv F P Q).hom.f 0 =
      (F.map (P.π.f 0)).app (Q.complex.X 0) ≫ (F.obj M).map (Q.π.f 0) := by
  rw [bifunctorTotalResolutionHomotopyEquiv_hom]
  simp only [HomologicalComplex.comp_f, Category.assoc]
  rw [ι_mapBifunctorMap_assoc, ι_mapBifunctorSingleLeftIso_hom_f_assoc]
  simp

end ASGinzburg
