import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-! Ordinary global dimension is the supremum of mathlib's actual
projective dimensions of all modules in the specified module universe.
No grading or finite-generation restriction is imposed. -/
namespace ASGinzburg
open CategoryTheory
universe u v
variable (R : Type u) [Ring R]

/-- Global dimension of the category of all ordinary left `R`-modules
whose underlying types lie in universe `v`. Right modules use `Rᵐᵒᵖ`. -/
noncomputable def ordinaryGlobalDimension : WithBot ℕ∞ :=
  ⨆ M : ModuleCat.{v} R, projectiveDimension M

theorem projectiveDimension_le_ordinaryGlobalDimension (M : ModuleCat.{v} R) :
    projectiveDimension M ≤ ordinaryGlobalDimension.{u,v} R :=
  le_iSup (fun N : ModuleCat.{v} R => projectiveDimension N) M

theorem ordinaryGlobalDimension_le_iff (d : WithBot ℕ∞) :
    ordinaryGlobalDimension.{u,v} R ≤ d ↔
      ∀ M : ModuleCat.{v} R, projectiveDimension M ≤ d :=
  iSup_le_iff

theorem ordinaryGlobalDimension_le_nat_iff (n : ℕ) :
    ordinaryGlobalDimension.{u,v} R ≤ n ↔
      ∀ M : ModuleCat.{v} R, HasProjectiveDimensionLE M n := by
  simp only [ordinaryGlobalDimension_le_iff, projectiveDimension_le_iff]

theorem ordinaryGlobalDimension_eq_of_bound_and_attained
    (d : WithBot ℕ∞)
    (hbound : ∀ M : ModuleCat.{v} R, projectiveDimension M ≤ d)
    (hattained : ∃ M : ModuleCat.{v} R, projectiveDimension M = d) :
    ordinaryGlobalDimension.{u,v} R = d := by
  obtain ⟨M, hM⟩ := hattained
  exact le_antisymm ((ordinaryGlobalDimension_le_iff R d).mpr hbound)
    (hM ▸ projectiveDimension_le_ordinaryGlobalDimension R M)

theorem ordinaryGlobalDimension_eq_nat_of_bound_and_attained
    (n : ℕ)
    (hbound : ∀ M : ModuleCat.{v} R, HasProjectiveDimensionLE M n)
    (hattained : ∃ M : ModuleCat.{v} R, projectiveDimension M = n) :
    ordinaryGlobalDimension.{u,v} R = n :=
  ordinaryGlobalDimension_eq_of_bound_and_attained R n
    (fun M => (projectiveDimension_le_iff M n).mpr (hbound M)) hattained

end ASGinzburg
