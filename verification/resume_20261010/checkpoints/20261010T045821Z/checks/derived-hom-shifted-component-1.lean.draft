import ASGinzburg.GradedLinearMapKernel

/-! Actual homogeneous linear maps of arbitrary integer degree commute
with the corresponding shifted homogeneous-component projections. -/
namespace ASGinzburg
open scoped DirectSum
universe u v w
variable (k : Type u) [Field k]
variable (M : Type v) [AddCommGroup M] [Module k M]
variable (N : Type w) [AddCommGroup N] [Module k N]
variable (G : ℤ → Submodule k M) [DirectSum.Decomposition G]
variable (H : ℤ → Submodule k N) [DirectSum.Decomposition H]

theorem homogeneousLinearMap_shifted_component
    (f : M →ₗ[k] N) (d : ℤ)
    (hf : ∀ p : ℤ, ∀ x : M, x ∈ G p → f x ∈ H (p + d)) (q : ℤ) :
    ∀ x : M, f (homogeneousComponent k M G q x) =
      homogeneousComponent k N H (q + d) (f x) := by
  intro x
  induction x using DirectSum.Decomposition.inductionOn G with
  | zero => rw [map_zero, map_zero, map_zero]
  | @homogeneous p x =>
    change f (DirectSum.decompose G (x : M) q : M) =
      (DirectSum.decompose H (f x) (q + d) : N)
    by_cases hp : p = q
    · subst p
      rw [DirectSum.decompose_of_mem_same G x.property,
        DirectSum.decompose_of_mem_same H (hf q x x.property)]
    · rw [DirectSum.decompose_of_mem_ne G x.property hp, map_zero,
        DirectSum.decompose_of_mem_ne H (hf p x x.property)
          (show p + d ≠ q + d from fun h => hp (add_right_cancel h))]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

end ASGinzburg
