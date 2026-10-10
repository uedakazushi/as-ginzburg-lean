import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-! A finite direct sum of objects of projective dimension at most `n`
has the same upper bound. This uses genuine Ext and its biproduct
comparison, so it applies to ordinary modules as well as graded modules. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

theorem finiteBiproduct_hasProjectiveDimensionLT {J : Type*} [Fintype J]
    (X : J → C) [HasBiproduct X] (n : ℕ) [∀ j, HasProjectiveDimensionLT (X j) n] :
    HasProjectiveDimensionLT (⨁ X) n := by
  letI := HasExt.standard C
  apply HasProjectiveDimensionLT.mk
  intro i hi Y e
  apply (Abelian.Ext.biproductAddEquiv (biproduct.isBilimit X) Y i).injective
  rw [map_zero]
  ext j
  change ((Abelian.Ext.mk₀ (biproduct.ι X j)).comp e (zero_add i))=0
  exact Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT _ n hi

end ASGinzburg
