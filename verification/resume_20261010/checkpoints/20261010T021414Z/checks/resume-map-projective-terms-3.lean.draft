import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Homology.Additive

/-! An exact additive functor transports a genuine projective resolution
when its actual terms have projective images. This does not require
preservation of every projective object. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
universe v w u u'
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{w} D] [Abelian D]
variable (F : C ⥤ D) [F.Additive] [F.PreservesHomology]

noncomputable def mapProjectiveResolutionOfTerms {X : C} (P : ProjectiveResolution X)
    (hP : ∀ n, Projective (F.obj (P.complex.X n))) :
    ProjectiveResolution (F.obj X) where
  complex := (F.mapHomologicalComplex _).obj P.complex
  projective := hP
  π := (F.mapHomologicalComplex _).map P.π ≫
    (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _
  quasiIso := inferInstance

theorem mapProjectiveResolutionOfTerms_isZero {X : C} (P : ProjectiveResolution X)
    (hP : ∀ n, Projective (F.obj (P.complex.X n))) (n : ℕ)
    (h : IsZero (P.complex.X n)) :
    IsZero ((mapProjectiveResolutionOfTerms F P hP).complex.X n) := by
  rw [IsZero.iff_id_eq_zero]
  change 𝟙 (F.obj (P.complex.X n)) = 0
  rw [← F.map_id, h.eq_of_src (𝟙 _) 0, F.map_zero]

end ASGinzburg
