import work.ASGinzburgDraft.BifunctorTotalHomotopyEquivalence
import work.ASGinzburgDraft.BifunctorTotalSingleLeft
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Homology.QuasiIso

/-! Contracting a projective resolution of a projective object in the
first variable of an actual total bifunctor complex. -/
namespace ASGinzburg
open CategoryTheory HomologicalComplex
variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]
variable [Abelian C₁] [Preadditive C₂] [Preadditive D]
variable (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
variable {M : C₁} [Projective M] (P : ProjectiveResolution M) (Q : ChainComplex C₂ ℕ)
variable [HasMapBifunctor P.complex Q F (ComplexShape.down ℕ)]

noncomputable def bifunctorTotalResolutionLeftHomotopyEquiv :
    HomotopyEquiv (mapBifunctor P.complex Q F (ComplexShape.down ℕ))
      (((F.obj M).mapHomologicalComplex (ComplexShape.down ℕ)).obj Q) := by
  letI : HasMapBifunctor (ProjectiveResolution.self M).complex Q F (ComplexShape.down ℕ) :=
    mapBifunctorSingleLeft_hasTotal F M Q
  exact (bifunctorTotalHomotopyEquivLeft F (ComplexShape.down ℕ)
    (ProjectiveResolution.homotopyEquiv P (ProjectiveResolution.self M)) Q).trans
      (HomotopyEquiv.ofIso (mapBifunctorSingleLeftIso F M Q))

theorem bifunctorTotalResolutionLeftHomotopyEquiv_hom :
    (bifunctorTotalResolutionLeftHomotopyEquiv F P Q).hom =
      mapBifunctorMap P.π (𝟙 Q) F (ComplexShape.down ℕ) ≫
        (mapBifunctorSingleLeftIso F M Q).hom := by
  letI : HasMapBifunctor (ProjectiveResolution.self M).complex Q F (ComplexShape.down ℕ) :=
    mapBifunctorSingleLeft_hasTotal F M Q
  have hh : (ProjectiveResolution.homotopyEquiv P (ProjectiveResolution.self M)).hom = P.π := by
    have h := ProjectiveResolution.homotopyEquiv_hom_π P (ProjectiveResolution.self M)
    change (ProjectiveResolution.homotopyEquiv P (ProjectiveResolution.self M)).hom ≫
      𝟙 ((ChainComplex.single₀ C₁).obj M) = P.π at h
    exact (Category.comp_id _).symm.trans h
  change mapBifunctorMap _ _ _ _ ≫ _ = _
  rw [hh]
  rfl

theorem bifunctorTotalResolutionLeft_quasiIso [CategoryWithHomology D] :
    QuasiIso (mapBifunctorMap P.π (𝟙 Q) F (ComplexShape.down ℕ) ≫
      (mapBifunctorSingleLeftIso F M Q).hom) := by
  rw [← bifunctorTotalResolutionLeftHomotopyEquiv_hom]
  infer_instance

end ASGinzburg
