import work.ASGinzburgDraft.BifunctorTotalResolutionLeft

/-! The canonical augmentation of the total bifunctor of two projective
resolutions of projective objects is a genuine homotopy equivalence.
For underlying vector-space resolutions the endpoint projectivity is
automatic; restriction from algebra modules still requires a separate
comparison with the actual enveloping total complex. -/
namespace ASGinzburg
open CategoryTheory HomologicalComplex
variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]
variable [Abelian C₁] [Abelian C₂] [Preadditive D] [CategoryTheory.Limits.HasZeroObject D]
variable (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
variable {M : C₁} {N : C₂} [Projective M] [Projective N]
variable (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
variable [HasMapBifunctor P.complex Q.complex F (ComplexShape.down ℕ)]

noncomputable def bifunctorTotalResolutionHomotopyEquiv :
    HomotopyEquiv (mapBifunctor P.complex Q.complex F (ComplexShape.down ℕ))
      ((ChainComplex.single₀ D).obj ((F.obj M).obj N)) :=
  ((bifunctorTotalResolutionLeftHomotopyEquiv F P Q.complex).trans
    ((F.obj M).mapHomotopyEquiv
      (ProjectiveResolution.homotopyEquiv Q (ProjectiveResolution.self N)))).trans
    (HomotopyEquiv.ofIso
      ((singleMapHomologicalComplex (F.obj M) (ComplexShape.down ℕ) 0).app N))

theorem bifunctorTotalResolutionHomotopyEquiv_hom :
    (bifunctorTotalResolutionHomotopyEquiv F P Q).hom =
      (mapBifunctorMap P.π (𝟙 Q.complex) F (ComplexShape.down ℕ) ≫
        (mapBifunctorSingleLeftIso F M Q.complex).hom) ≫
      ((F.obj M).mapHomologicalComplex (ComplexShape.down ℕ)).map Q.π ≫
      (singleMapHomologicalComplex (F.obj M) (ComplexShape.down ℕ) 0).hom.app N := by
  have hh : (ProjectiveResolution.homotopyEquiv Q (ProjectiveResolution.self N)).hom = Q.π := by
    have h := ProjectiveResolution.homotopyEquiv_hom_π Q (ProjectiveResolution.self N)
    exact (Category.comp_id _).symm.trans h
  change ((bifunctorTotalResolutionLeftHomotopyEquiv F P Q.complex).hom ≫
    ((F.obj M).mapHomotopyEquiv _).hom) ≫ _ = _
  rw [bifunctorTotalResolutionLeftHomotopyEquiv_hom]
  change (_ ≫ ((F.obj M).mapHomologicalComplex _).map
    (ProjectiveResolution.homotopyEquiv Q (ProjectiveResolution.self N)).hom) ≫ _ = _
  rw [hh]
  exact Category.assoc _ _ _

theorem bifunctorTotalResolution_quasiIso [CategoryWithHomology D] :
    QuasiIso ((mapBifunctorMap P.π (𝟙 Q.complex) F (ComplexShape.down ℕ) ≫
      (mapBifunctorSingleLeftIso F M Q.complex).hom) ≫
      ((F.obj M).mapHomologicalComplex (ComplexShape.down ℕ)).map Q.π ≫
      (singleMapHomologicalComplex (F.obj M) (ComplexShape.down ℕ) 0).hom.app N) := by
  rw [← bifunctorTotalResolutionHomotopyEquiv_hom]
  infer_instance

end ASGinzburg
