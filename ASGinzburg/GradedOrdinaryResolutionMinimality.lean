import ASGinzburg.GradedOrdinaryMinimalResolution

/-! Every actual differential of the recursively constructed resolution
has image in the genuine ideal-action span, including off-shape maps. -/
namespace ASGinzburg.GradedOrdinaryBoundedModule
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]
variable {A : ℤ → Submodule k R} {b : ℤ} {J : Ideal R}
variable (C : ∀ M : GradedOrdinaryBoundedModule k R A b,
  GradedOrdinaryProjectiveCover M.val b J)
variable (M : GradedOrdinaryBoundedModule k R A b)

theorem resolution_d_minimal_all (i j : ℕ) (x : (resolution C M).complex.X i) :
    (resolution C M).complex.d i j x ∈
      ordinaryIdealActionSpan k R ((resolution C M).complex.X j) J := by
  by_cases h : i = j + 1
  · subst i
    exact resolution_d_minimal C M j x
  · have hshape : ¬ (ComplexShape.down ℕ).Rel i j := by
      simpa only [ComplexShape.down_Rel, eq_comm] using h
    rw [(resolution C M).complex.shape i j hshape]
    exact (ordinaryIdealActionSpan k R ((resolution C M).complex.X j) J).zero_mem

end ASGinzburg.GradedOrdinaryBoundedModule
