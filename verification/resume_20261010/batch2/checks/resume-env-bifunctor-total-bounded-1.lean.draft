import Mathlib.Algebra.Homology.Bifunctor
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! Actual first-quadrant tensor totals vanish above the sum of the
genuine vanishing bounds of their factor complexes. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]
variable [Preadditive C₁] [Preadditive C₂] [Preadditive D]
variable (P : ChainComplex C₁ ℕ) (Q : ChainComplex C₂ ℕ)
variable (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
variable [HasMapBifunctor P Q F (ComplexShape.down ℕ)]

theorem bifunctorTotal_isZero_of_bounded (a b : ℕ)
    (hP : ∀ i, a < i → IsZero (P.X i)) (hQ : ∀ j, b < j → IsZero (Q.X j))
    (n : ℕ) (hn : a + b < n) :
    IsZero ((mapBifunctor P Q F (ComplexShape.down ℕ)).X n) := by
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  apply IsZero.eq_of_src
  have hsum : i + j = n := hij
  by_cases hi : a < i
  · exact (F.flip.obj (Q.X j)).map_isZero (hP i hi)
  · have hj : b < j := by omega
    exact (F.obj (P.X i)).map_isZero (hQ j hj)

end ASGinzburg
