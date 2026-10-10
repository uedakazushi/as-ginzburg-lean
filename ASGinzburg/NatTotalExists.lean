import ASGinzburg.TensorTotalFinite
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-! Actual total complexes of first-quadrant bicomplexes need only finite
coproducts: each diagonal of the addition map on natural numbers is finite. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {C C₁ C₂ D : Type*} [Category C] [Category C₁] [Category C₂] [Category D]
  [Preadditive C] [Preadditive C₁] [Preadditive C₂] [Preadditive D]

instance natBicomplex_hasTotal [HasFiniteCoproducts C]
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)) :
    K.HasTotal (ComplexShape.down ℕ) := fun _ => by infer_instance

instance nat_hasMapBifunctor [HasFiniteCoproducts D]
    (K₁ : ChainComplex C₁ ℕ) (K₂ : ChainComplex C₂ ℕ) (F : C₁ ⥤ C₂ ⥤ D)
    [F.Additive] [∀ X, (F.obj X).Additive] :
    HasMapBifunctor K₁ K₂ F (ComplexShape.down ℕ) := by
  apply natBicomplex_hasTotal

end ASGinzburg
