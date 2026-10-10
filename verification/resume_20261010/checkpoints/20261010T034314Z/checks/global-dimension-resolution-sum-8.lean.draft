import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.RingTheory.Finiteness.Basic

/-! Finite biproducts of actual projective resolutions are actual
projective resolutions. The construction retains the original terms. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {J : Type} [Fintype J]
attribute [local instance] Abelian.hasFiniteBiproducts

omit [Fintype J] in
theorem functor_mapBiproduct_morphism {D : Type*} [Category D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] {X Y : J → C} [HasBiproduct X] [HasBiproduct Y]
    [PreservesBiproduct X F] [PreservesBiproduct Y F] (f : ∀ j, X j ⟶ Y j) :
    F.map (biproduct.map f)=
      (F.mapBiproduct X).hom ≫ biproduct.map (f := F.obj ∘ X) (g := F.obj ∘ Y)
        (fun j => F.map (f j)) ≫
        (F.mapBiproduct Y).inv := by
  apply (cancel_mono (F.mapBiproduct Y).hom).mp
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  apply biproduct.hom_ext
  intro j
  have hY : (F.mapBiproduct Y).hom ≫ biproduct.π (F.obj ∘ Y) j=
      F.map (biproduct.π Y j) :=
    biproduct.lift_π (fun j => F.map (biproduct.π Y j)) j
  have hX : (F.mapBiproduct X).hom ≫ biproduct.π (F.obj ∘ X) j=
      F.map (biproduct.π X j) :=
    biproduct.lift_π (fun j => F.map (biproduct.π X j)) j
  calc
    (F.map (biproduct.map f) ≫ (F.mapBiproduct Y).hom) ≫ biproduct.π (F.obj ∘ Y) j=
        F.map (biproduct.map f) ≫ F.map (biproduct.π Y j) := by rw [Category.assoc,hY]
    _=F.map (biproduct.π X j) ≫ F.map (f j) := by
      rw [← F.map_comp,biproduct.map_π,F.map_comp]
    _=((F.mapBiproduct X).hom ≫ biproduct.map (f := F.obj ∘ X) (g := F.obj ∘ Y)
        (fun j => F.map (f j))) ≫ biproduct.π (F.obj ∘ Y) j := by
      rw [Category.assoc,biproduct.map_π,← Category.assoc,hX]

theorem finiteBiproduct_projective (X : J → C) [∀ j, Projective (X j)] :
    Projective (⨁ X) where
  factors f g _ := by
    refine ⟨biproduct.desc (fun j => Projective.factorThru (biproduct.ι X j ≫ f) g), ?_⟩
    apply biproduct.hom_ext'
    intro j
    simp only [← Category.assoc,biproduct.ι_desc,Projective.factorThru_comp]

theorem finiteBiproduct_quasiIso {X Y : J → ChainComplex C ℕ}
    (f : ∀ j, X j ⟶ Y j) [∀ j, QuasiIso (f j)] :
    QuasiIso (biproduct.map f) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  change IsIso ((HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n).map
    (biproduct.map f))
  rw [functor_mapBiproduct_morphism]
  haveI : ∀ j, IsIso ((HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n).map
      (f j)) := by
    intro j
    change IsIso (HomologicalComplex.homologyMap (f j) n)
    exact (quasiIsoAt_iff_isIso_homologyMap (f j) n).mp inferInstance
  haveI : IsIso (biproduct.map
      (f := (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n).obj ∘ X)
      (g := (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n).obj ∘ Y)
      (fun j => (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n).map (f j))) := by
    change IsIso ((biproduct.mapIso
      (f := (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n).obj ∘ X)
      (g := (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n).obj ∘ Y)
      (fun j => asIso
      ((HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n).map (f j)))).hom)
    infer_instance
  infer_instance

noncomputable def finiteBiproductProjectiveResolution (X : J → C)
    (P : ∀ j, ProjectiveResolution (X j)) : ProjectiveResolution (⨁ X) where
  complex := ⨁ (fun j => (P j).complex)
  projective n := by
    let e := (HomologicalComplex.eval C (ComplexShape.down ℕ) n).mapBiproduct
      (fun j => (P j).complex)
    haveI : ∀ j, Projective (((HomologicalComplex.eval C (ComplexShape.down ℕ) n).obj ∘
        (fun j => (P j).complex)) j) := fun j => (P j).projective n
    exact Projective.of_iso e.symm (finiteBiproduct_projective _)
  π := biproduct.map (fun j => (P j).π) ≫ ((ChainComplex.single₀ C).mapBiproduct X).inv
  quasiIso := by
    letI := finiteBiproduct_quasiIso (fun j => (P j).π)
    infer_instance

noncomputable def finiteBiproductProjectiveResolutionTermIso (X : J → C)
    (P : ∀ j, ProjectiveResolution (X j)) (n : ℕ) :
    (finiteBiproductProjectiveResolution X P).complex.X n ≅
      ⨁ (fun j => (P j).complex.X n) :=
  (HomologicalComplex.eval C (ComplexShape.down ℕ) n).mapBiproduct
    (fun j => (P j).complex)

theorem finiteBiproductProjectiveResolution_isZero (X : J → C)
    (P : ∀ j, ProjectiveResolution (X j)) (n : ℕ)
    (h : ∀ j, IsZero ((P j).complex.X n)) :
    IsZero ((finiteBiproductProjectiveResolution X P).complex.X n) := by
  apply IsZero.of_iso _ (finiteBiproductProjectiveResolutionTermIso X P n)
  rw [IsZero.iff_id_eq_zero]
  apply biproduct.hom_ext
  intro j
  exact (h j).eq_of_tgt _ _

noncomputable def projectiveResolutionAlongIso {X Y : C}
    (P : ProjectiveResolution X) (e : X ≅ Y) : ProjectiveResolution Y where
  complex := P.complex
  projective := P.projective
  π := P.π ≫ (ChainComplex.single₀ C).map e.hom

end ASGinzburg

namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
universe w z
variable {R : Type w} [Ring R] {J : Type} [Fintype J]

theorem finiteBiproductProjectiveResolution_finite (X : J → ModuleCat.{z} R)
    (P : ∀ j, ProjectiveResolution (X j)) (n : ℕ)
    (h : ∀ j, Module.Finite R ((P j).complex.X n)) :
    Module.Finite R ((finiteBiproductProjectiveResolution X P).complex.X n) := by
  letI := h
  let e := finiteBiproductProjectiveResolutionTermIso X P n ≪≫
    ModuleCat.biproductIsoPi (fun j => (P j).complex.X n)
  exact Module.Finite.equiv e.symm.toLinearEquiv

end ASGinzburg
