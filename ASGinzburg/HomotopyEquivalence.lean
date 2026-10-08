import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.CategoryTheory.Whiskering
namespace ASGinzburg
open CategoryTheory CategoryTheory.Functor
universe u v u' v'
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Preadditive C] [Preadditive D] {I : Type*}

def homotopyMapUnitIso (e : C ≌ D) [e.functor.Additive] (c : ComplexShape I) :
    𝟭 (HomotopyCategory C c) ≅ e.functor.mapHomotopyCategory c ⋙ e.inverse.mapHomotopyCategory c :=
  CategoryTheory.Quotient.natIsoLift (homotopic C c)
    (isoWhiskerRight (e.mapHomologicalComplex c).unitIso (HomotopyCategory.quotient C c))

def homotopyMapCounitIso (e : C ≌ D) [e.functor.Additive] (c : ComplexShape I) :
    e.inverse.mapHomotopyCategory c ⋙ e.functor.mapHomotopyCategory c ≅ 𝟭 (HomotopyCategory D c) :=
  CategoryTheory.Quotient.natIsoLift (homotopic D c)
    (isoWhiskerRight (e.mapHomologicalComplex c).counitIso (HomotopyCategory.quotient D c))

def homotopyMapEquivalence (e : C ≌ D) [e.functor.Additive] (c : ComplexShape I) :
    HomotopyCategory C c ≌ HomotopyCategory D c :=
  CategoryTheory.Equivalence.mk (e.functor.mapHomotopyCategory c)
    (e.inverse.mapHomotopyCategory c) (homotopyMapUnitIso e c) (homotopyMapCounitIso e c)

instance homotopyMapAdditive (F : C ⥤ D) [F.Additive] (c : ComplexShape I) :
    (F.mapHomotopyCategory c).Additive where
  map_add := by
    intro X Y f g
    obtain ⟨f',hf⟩ := (HomotopyCategory.quotient C c).map_surjective f
    obtain ⟨g',hg⟩ := (HomotopyCategory.quotient C c).map_surjective g
    rw [← hf, ← hg, ← (HomotopyCategory.quotient C c).map_add]
    rw [Functor.mapHomotopyCategory_map]
    rw [(F.mapHomologicalComplex c).map_add, (HomotopyCategory.quotient D c).map_add]
    rw [Functor.mapHomotopyCategory_map, Functor.mapHomotopyCategory_map]
end ASGinzburg
