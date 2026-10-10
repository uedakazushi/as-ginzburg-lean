import Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.Single

/-! Totalizing an additive bifunctor with its first complex concentrated
in degree zero gives the ordinary mapped second complex. -/
namespace ASGinzburg
open CategoryTheory Category Limits HomologicalComplex

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D] [HasZeroObject C₁]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  (M : C₁) (K : ChainComplex C₂ ℕ)

noncomputable abbrev mapBifunctorSingleLeftBicomplex :=
  ((F.mapBifunctorHomologicalComplex (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj
    ((ChainComplex.single₀ C₁).obj M)).obj K

noncomputable def mapBifunctorSingleLeftCofan (n : ℕ) :
    (mapBifunctorSingleLeftBicomplex F M K).toGradedObject.CofanMapObjFun
      (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)) n :=
  GradedObject.CofanMapObjFun.mk _ _ n ((F.obj M).obj (K.X n)) (fun a ha =>
    if h : a.1 = 0 then
      eqToHom (by
        rcases a with ⟨i, j⟩
        dsimp at h
        subst i
        have hj : j = n := by simpa using ha
        subst j
        rfl)
    else 0)

noncomputable def mapBifunctorSingleLeftCofanIsColimit (n : ℕ) :
    IsColimit (mapBifunctorSingleLeftCofan F M K n) :=
  mkCofanColimit _
    (fun s => s.inj ⟨⟨0, n⟩, by simp⟩)
    (fun s => by
      rintro ⟨⟨i, j⟩, h⟩
      by_cases hi : i = 0
      · subst i
        have hj : j = n := by simpa using h
        subst j
        simp [mapBifunctorSingleLeftCofan, GradedObject.CofanMapObjFun.mk]
      · apply IsZero.eq_of_src
        exact (F.flip.obj (K.X j)).map_isZero
          (isZero_single_obj_X (ComplexShape.down ℕ) 0 M i hi))
    (fun s m hm => by
      simpa [mapBifunctorSingleLeftCofan, GradedObject.CofanMapObjFun.mk] using
        hm ⟨⟨0, n⟩, by simp⟩)

instance mapBifunctorSingleLeft_hasTotal :
    HasMapBifunctor ((ChainComplex.single₀ C₁).obj M) K F (ComplexShape.down ℕ) :=
  GradedObject.CofanMapObjFun.hasMap _ _ _ (mapBifunctorSingleLeftCofanIsColimit F M K)

noncomputable def mapBifunctorSingleLeftXIso (n : ℕ) :
    (mapBifunctor ((ChainComplex.single₀ C₁).obj M) K F (ComplexShape.down ℕ)).X n ≅
      (F.obj M).obj (K.X n) :=
  (GradedObject.CofanMapObjFun.iso (mapBifunctorSingleLeftCofanIsColimit F M K n)).symm

theorem mapBifunctorSingleLeftXIso_inv (n : ℕ) :
    (mapBifunctorSingleLeftXIso F M K n).inv =
      ιMapBifunctor ((ChainComplex.single₀ C₁).obj M) K F (ComplexShape.down ℕ)
        0 n n (by simp) := rfl

theorem mapBifunctorSingleLeftXIso_inv_comm (i j : ℕ) :
    (mapBifunctorSingleLeftXIso F M K i).inv ≫
        (mapBifunctor ((ChainComplex.single₀ C₁).obj M) K F (ComplexShape.down ℕ)).d i j =
      (F.obj M).map (K.d i j) ≫ (mapBifunctorSingleLeftXIso F M K j).inv := by
  by_cases hij : (ComplexShape.down ℕ).Rel i j
  · rw [mapBifunctorSingleLeftXIso_inv, mapBifunctorSingleLeftXIso_inv,
      mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
      mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ (by simp), zero_add,
      mapBifunctor.d₂_eq _ _ _ _ _ hij _ (by simp)]
    simp
  · rw [HomologicalComplex.shape _ _ _ hij, K.shape _ _ hij,
      Functor.map_zero, comp_zero, zero_comp]

noncomputable def mapBifunctorSingleLeftIso :
    mapBifunctor ((ChainComplex.single₀ C₁).obj M) K F (ComplexShape.down ℕ) ≅
      ((F.obj M).mapHomologicalComplex (ComplexShape.down ℕ)).obj K :=
  (HomologicalComplex.Hom.isoOfComponents
    (fun n => (mapBifunctorSingleLeftXIso F M K n).symm)
    (fun i j _ => mapBifunctorSingleLeftXIso_inv_comm F M K i j)).symm

theorem mapBifunctorSingleLeftIso_inv_f (n : ℕ) :
    (mapBifunctorSingleLeftIso F M K).inv.f n =
      ιMapBifunctor ((ChainComplex.single₀ C₁).obj M) K F (ComplexShape.down ℕ)
        0 n n (by simp) := rfl

@[reassoc (attr := simp)]
theorem ι_mapBifunctorSingleLeftIso_hom_f (n : ℕ) :
    ιMapBifunctor ((ChainComplex.single₀ C₁).obj M) K F (ComplexShape.down ℕ)
        0 n n (by simp) ≫ (mapBifunctorSingleLeftIso F M K).hom.f n = 𝟙 _ :=
  (mapBifunctorSingleLeftXIso F M K n).inv_hom_id

theorem mapBifunctorSingleLeftIso_inv_naturality {L : ChainComplex C₂ ℕ}
    (f : K ⟶ L) :
    ((F.obj M).mapHomologicalComplex (ComplexShape.down ℕ)).map f ≫
        (mapBifunctorSingleLeftIso F M L).inv =
      (mapBifunctorSingleLeftIso F M K).inv ≫
        mapBifunctorMap (𝟙 ((ChainComplex.single₀ C₁).obj M)) f F (ComplexShape.down ℕ) := by
  ext n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    mapBifunctorSingleLeftIso_inv_f, mapBifunctorSingleLeftIso_inv_f, ι_mapBifunctorMap]
  simp

theorem mapBifunctorSingleLeftIso_naturality {L : ChainComplex C₂ ℕ} (f : K ⟶ L) :
    mapBifunctorMap (𝟙 ((ChainComplex.single₀ C₁).obj M)) f F (ComplexShape.down ℕ) ≫
        (mapBifunctorSingleLeftIso F M L).hom =
      (mapBifunctorSingleLeftIso F M K).hom ≫
        ((F.obj M).mapHomologicalComplex (ComplexShape.down ℕ)).map f := by
  apply (cancel_mono (mapBifunctorSingleLeftIso F M L).inv).mp
  rw [assoc, Iso.hom_inv_id, comp_id, assoc,
    mapBifunctorSingleLeftIso_inv_naturality]
  simp

end ASGinzburg
