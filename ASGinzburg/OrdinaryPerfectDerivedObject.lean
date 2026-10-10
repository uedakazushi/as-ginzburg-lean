import ASGinzburg.OrdinaryPerfectComplex
import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! Genuine bounded finite projective cochain complexes define perfect
objects in the actual derived category of ordinary modules. -/
namespace ASGinzburg
open CategoryTheory
universe v w
variable (R : Type v) [Ring R]
variable [HasDerivedCategory.{w} (ModuleCat.{v} R)]

def ordinaryPerfectDerivedProperty (X : DerivedCategory (ModuleCat.{v} R)) : Prop :=
  ∃ K : CochainComplex (ModuleCat.{v} R) ℤ,
    ordinaryFiniteProjectiveCochainProperty R K ∧
      Nonempty (DerivedCategory.Q.obj K ≅ X)

theorem ordinaryPerfectDerivedProperty_of_cochain
    (K : CochainComplex (ModuleCat.{v} R) ℤ)
    (hK : ordinaryFiniteProjectiveCochainProperty R K) :
    ordinaryPerfectDerivedProperty R (DerivedCategory.Q.obj K) :=
  ⟨K, hK, ⟨Iso.refl _⟩⟩

theorem ordinaryPerfectDerivedProperty_of_iso
    {X Y : DerivedCategory (ModuleCat.{v} R)} (e : X ≅ Y)
    (hY : ordinaryPerfectDerivedProperty R Y) : ordinaryPerfectDerivedProperty R X := by
  obtain ⟨K, hK, ⟨eK⟩⟩ := hY
  exact ⟨K, hK, ⟨eK ≪≫ e.symm⟩⟩

theorem ordinaryPerfectModuleProperty_derived_single
    (X : ModuleCat.{v} R) (hX : ordinaryPerfectModuleProperty R X) :
    ordinaryPerfectDerivedProperty R
      (DerivedCategory.Q.obj
        ((HomologicalComplex.single (ModuleCat R) (ComplexShape.up ℤ) 0).obj X)) := by
  obtain ⟨K, hK, f, hf⟩ := hX
  letI := hf
  exact ⟨K, hK, ⟨asIso (DerivedCategory.Q.map f)⟩⟩

theorem ordinaryPerfectModuleProperty_derived_degree_zero
    (X : ModuleCat.{v} R) (hX : ordinaryPerfectModuleProperty R X) :
    ordinaryPerfectDerivedProperty R
      ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj X) := by
  apply ordinaryPerfectDerivedProperty_of_iso R
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) 0).app X)
  exact ordinaryPerfectModuleProperty_derived_single R X hX

end ASGinzburg
