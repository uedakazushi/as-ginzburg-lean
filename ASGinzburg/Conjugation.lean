import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.Tactic

/-!
# Multiplicative transport by object isomorphisms

This is the formal content of (3.3), once the fully faithful functor and
object isomorphisms have actually been constructed. The construction of
the tilting equivalence and the inverse Serre functor is not included.
-/

namespace ASGinzburg

open CategoryTheory

universe u₁ u₂ v₁ v₂ w t

variable {k : Type w} [Field k]
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Preadditive C] [Preadditive D] [Linear k C] [Linear k D]
variable (F : C ⥤ D) [F.Full] [F.Faithful] [F.Additive] [F.Linear k]
variable {I : Type t} (X : I → C) (Y : I → D) (η : ∀ i, F.obj (X i) ≅ Y i)

noncomputable def conjugateHom (i j : I) : (X i ⟶ X j) ≃ₗ[k] (Y i ⟶ Y j) :=
  (LinearEquiv.ofBijective (F.mapLinearMap k)
    ⟨F.map_injective, F.map_surjective⟩).trans (Linear.homCongr k (η i) (η j))

theorem conjugateHom_apply (i j : I) (f : X i ⟶ X j) :
    conjugateHom (k := k) F X Y η i j f = (η i).inv ≫ F.map f ≫ (η j).hom := by
  change ((η i).inv ≫ F.map f) ≫ (η j).hom = _
  exact Category.assoc _ _ _

theorem conjugateHom_id (i : I) :
    conjugateHom (k := k) F X Y η i i (𝟙 (X i)) = 𝟙 (Y i) := by
  simp [conjugateHom_apply]

theorem conjugateHom_comp (i j l : I) (f : X i ⟶ X j) (g : X j ⟶ X l) :
    conjugateHom (k := k) F X Y η i l (f ≫ g) =
      conjugateHom (k := k) F X Y η i j f ≫ conjugateHom (k := k) F X Y η j l g := by
  simp [conjugateHom_apply, F.map_comp, Category.assoc]

end ASGinzburg
