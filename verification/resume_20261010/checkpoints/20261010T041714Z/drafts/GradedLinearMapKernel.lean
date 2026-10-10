import work.ASGinzburgDraft.HomogeneousSubmoduleDecomposition
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Module.Submodule.RestrictScalars

/-! Grade-preserving actual maps commute with every homogeneous component.
Their genuine concrete kernels are homogeneous and inherit a direct-sum
grading, including for ordinary ring-linear maps. -/
namespace ASGinzburg
open CategoryTheory
open scoped DirectSum ModuleCat.Algebra
universe u v w z
variable (k : Type u) [Field k]
variable (M : Type v) [AddCommGroup M] [Module k M]
variable (N : Type w) [AddCommGroup N] [Module k N]
variable (G : ℤ → Submodule k M) [DirectSum.Decomposition G]
variable (H : ℤ → Submodule k N) [DirectSum.Decomposition H]

noncomputable def homogeneousComponent (q : ℤ) : M →ₗ[k] M :=
  (G q).subtype.comp ((DirectSum.component k ℤ (fun p => G p) q).comp
    (DirectSum.decomposeLinearEquiv G).toLinearMap)

theorem homogeneousLinearMap_component
    (f : M →ₗ[k] N) (hf : ∀ q : ℤ, ∀ x : M, x ∈ G q → f x ∈ H q)
    (q : ℤ) :
    ∀ x : M, f (homogeneousComponent k M G q x) =
      homogeneousComponent k N H q (f x) := by
  intro x
  induction x using DirectSum.Decomposition.inductionOn G with
  | zero => rw [map_zero, map_zero, map_zero]
  | @homogeneous p x =>
    change f (DirectSum.decompose G (x : M) q : M) =
      (DirectSum.decompose H (f x) q : N)
    by_cases hp : p = q
    · subst p
      rw [DirectSum.decompose_of_mem_same G x.property,
        DirectSum.decompose_of_mem_same H (hf q x x.property)]
    · rw [DirectSum.decompose_of_mem_ne G x.property hp, map_zero,
        DirectSum.decompose_of_mem_ne H (hf p x x.property) hp]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

theorem homogeneousLinearMap_kernel_component_mem
    (f : M →ₗ[k] N) (hf : ∀ q : ℤ, ∀ x : M, x ∈ G q → f x ∈ H q)
    (q : ℤ) (x : M) (hx : x ∈ (LinearMap.ker f)) :
    (DirectSum.decompose G x q : M) ∈ (LinearMap.ker f) := by
  change f (homogeneousComponent k M G q x) = 0
  rw [homogeneousLinearMap_component k M N G H f hf q x,
    LinearMap.mem_ker.mp hx, map_zero]

noncomputable def homogeneousLinearMapKernelDecomposition
    (f : M →ₗ[k] N) (hf : ∀ q : ℤ, ∀ x : M, x ∈ G q → f x ∈ H q) :
    DirectSum.Decomposition (homogeneousSubmoduleGrade k M G (LinearMap.ker f)) :=
  homogeneousSubmoduleDecomposition k M G (LinearMap.ker f)
    (homogeneousLinearMap_kernel_component_mem k M N G H f hf)

variable (R : Type z) [Ring R] [Algebra k R]

noncomputable def ordinaryHomogeneousKernelDecomposition
    {U V : ModuleCat.{v} R}
    (G₀ : ℤ → Submodule k U) [DirectSum.Decomposition G₀]
    (H₀ : ℤ → Submodule k V) [DirectSum.Decomposition H₀]
    (f : U ⟶ V) (hf : ∀ q : ℤ, ∀ x : U, x ∈ G₀ q → f x ∈ H₀ q) :
    DirectSum.Decomposition
      (homogeneousSubmoduleGrade k U G₀ ((LinearMap.ker f.hom).restrictScalars k)) :=
  homogeneousSubmoduleDecomposition k U G₀ ((LinearMap.ker f.hom).restrictScalars k)
    (fun q x hx => homogeneousLinearMap_kernel_component_mem k U V G₀ H₀
      (f.hom.restrictScalars k) hf q x hx)

end ASGinzburg
