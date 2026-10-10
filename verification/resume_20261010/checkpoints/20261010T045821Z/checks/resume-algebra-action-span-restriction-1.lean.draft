import work.ASGinzburgDraft.AlgebraModuleRestrictionComparison
import Mathlib.LinearAlgebra.Span.Basic

/-! The identity scalar-restriction comparison preserves spans. This
keeps the original k-linear radical span compatible with ModuleCat's
canonical k-action induced by an algebra map. -/
namespace ASGinzburg
open CategoryTheory
universe u v w
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module R M]
  [IsScalarTower k R M]

theorem algebraModuleRestrictScalarsIso_inv_mem_span
    (s : Set M) {x : M} (hx : x ∈ Submodule.span k s) :
    (algebraModuleRestrictScalarsIso k R M).inv x ∈
      Submodule.span k {y : (ModuleCat.restrictScalars (algebraMap k R)).obj
        (ModuleCat.of R M) | (y : M) ∈ s} := by
  have h := Submodule.apply_mem_span_image_of_mem_span
    (algebraModuleRestrictScalarsIso k R M).inv.hom hx
  apply Submodule.span_mono _ h
  rintro y ⟨z, hz, rfl⟩
  exact hz

theorem algebraModuleRestrictScalarsIso_inv_mem_actionSpan
    (I : Set R) {x : M}
    (hx : x ∈ Submodule.span k {a : M | ∃ r ∈ I, ∃ m : M, r • m = a}) :
    (algebraModuleRestrictScalarsIso k R M).inv x ∈
      Submodule.span k {a : (ModuleCat.restrictScalars (algebraMap k R)).obj
        (ModuleCat.of R M) | ∃ r ∈ I, ∃ m : M, r • m = (a : M)} :=
  algebraModuleRestrictScalarsIso_inv_mem_span k R M _ hx

end ASGinzburg
