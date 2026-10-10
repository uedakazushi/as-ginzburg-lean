import work.ASGinzburgDraft.GradedLinearMapKernel

/-! The concrete image of a grade-preserving actual linear map is
homogeneous, and therefore inherits the genuine internal decomposition. -/
namespace ASGinzburg
open scoped DirectSum ModuleCat.Algebra
open CategoryTheory
universe u v w z
variable (k : Type u) [Field k]
variable (M : Type v) [AddCommGroup M] [Module k M]
variable (N : Type w) [AddCommGroup N] [Module k N]
variable (G : ℤ → Submodule k M) [DirectSum.Decomposition G]
variable (H : ℤ → Submodule k N) [DirectSum.Decomposition H]

theorem homogeneousLinearMap_range_component_mem
    (f : M →ₗ[k] N) (hf : ∀ q : ℤ, ∀ x : M, x ∈ G q → f x ∈ H q)
    (q : ℤ) (x : N) (hx : x ∈ LinearMap.range f) :
    (DirectSum.decompose H x q : N) ∈ LinearMap.range f := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨homogeneousComponent k M G q y,
    homogeneousLinearMap_component k M N G H f hf q y⟩

noncomputable def homogeneousLinearMapRangeDecomposition
    (f : M →ₗ[k] N) (hf : ∀ q : ℤ, ∀ x : M, x ∈ G q → f x ∈ H q) :
    DirectSum.Decomposition (homogeneousSubmoduleGrade k N H (LinearMap.range f)) :=
  homogeneousSubmoduleDecomposition k N H (LinearMap.range f)
    (homogeneousLinearMap_range_component_mem k M N G H f hf)

variable (R : Type z) [Ring R] [Algebra k R]

noncomputable def ordinaryHomogeneousRangeDecomposition
    {U V : ModuleCat.{v} R}
    (G₀ : ℤ → Submodule k U) [DirectSum.Decomposition G₀]
    (H₀ : ℤ → Submodule k V) [DirectSum.Decomposition H₀]
    (f : U ⟶ V) (hf : ∀ q : ℤ, ∀ x : U, x ∈ G₀ q → f x ∈ H₀ q) :
    DirectSum.Decomposition
      (homogeneousSubmoduleGrade k V H₀ ((LinearMap.range f.hom).restrictScalars k)) :=
  homogeneousSubmoduleDecomposition k V H₀ ((LinearMap.range f.hom).restrictScalars k)
    (fun q x hx => homogeneousLinearMap_range_component_mem k U V G₀ H₀
      (f.hom.restrictScalars k) hf q x hx)

end ASGinzburg
