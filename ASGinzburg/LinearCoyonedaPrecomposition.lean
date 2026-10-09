import ASGinzburg.LinearRepresentationEquivalence
import Mathlib.CategoryTheory.Adjunction.Basic

/-! Actual representable module-valued functors are transported by linear
precomposition using the actual adjunction hom-set isomorphism. -/
namespace ASGinzburg
open CategoryTheory Opposite
universe u v w z
variable {k : Type u} [Field k]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable {D : Type z} [Category.{v} D] [Preadditive D] [Linear k D]
variable (E : C ≌ D) [E.functor.Linear k] [E.functor.Additive]

noncomputable def linearAdjunctionHomEquiv (X : C) (Y : D) :
    (X ⟶ E.inverse.obj Y) ≃ₗ[k] (E.functor.obj X ⟶ Y) where
  toEquiv := (E.toAdjunction.homEquiv X Y).symm
  map_add' f g := by
    change E.functor.map (f+g) ≫ E.counit.app Y = _
    simp only [Functor.map_add, Preadditive.add_comp]
    rfl
  map_smul' r f := by
    change E.functor.map (r • f) ≫ E.counit.app Y = _
    simp only [Functor.map_smul, Linear.smul_comp]
    rfl

noncomputable def linearCoyonedaPrecompositionIso (X : C) :
    E.inverse ⋙ (linearCoyoneda k C).obj (op X) ≅
      (linearCoyoneda k D).obj (op (E.functor.obj X)) :=
  NatIso.ofComponents (fun Y => (linearAdjunctionHomEquiv (k := k) E X Y).toModuleIso)
    (by
      intro Y Z g
      apply ModuleCat.hom_ext
      ext f
      change linearAdjunctionHomEquiv (k := k) E X Z (f ≫ E.inverse.map g) =
        linearAdjunctionHomEquiv (k := k) E X Y f ≫ g
      exact E.toAdjunction.homEquiv_naturality_right_symm f g)

end ASGinzburg
