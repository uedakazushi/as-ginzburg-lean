import ASGinzburg.HomogeneousCore
import Mathlib.Algebra.Module.Submodule.RestrictScalars

/-! The homogeneous components of finitely many actual vectors form a
finite set. Their ordinary ring span has a homogeneous core containing
the original vectors, without a grading assumption on that ring. -/
namespace ASGinzburg
open scoped DirectSum
universe u v w
variable (k : Type u) [Field k] (M : Type v) [AddCommGroup M] [Module k M]
variable (G : ℤ → Submodule k M) [DirectSum.Decomposition G]
variable (n : ℕ) (x : Fin n → M)

noncomputable def finiteHomogeneousComponents : Finset M := by
  classical
  exact Finset.univ.biUnion fun i : Fin n =>
    (DirectSum.decompose G (x i)).support.image
      (fun q : ℤ => (DirectSum.decompose G (x i) q : M))

theorem component_mem_finiteHomogeneousComponents_or_zero (i : Fin n) (q : ℤ) :
    (DirectSum.decompose G (x i) q : M) ∈ finiteHomogeneousComponents k M G n x ∨
      (DirectSum.decompose G (x i) q : M)=0 := by
  classical
  by_cases hq : q ∈ (DirectSum.decompose G (x i)).support
  · apply Or.inl
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,
      Finset.mem_image.mpr ⟨q,hq,rfl⟩⟩
  · apply Or.inr
    have hz : DirectSum.decompose G (x i) q=0 := DFinsupp.notMem_support_iff.mp hq
    exact congrArg (fun z : G q => (z : M)) hz

variable (R : Type w) [Ring R] [Algebra k R] [Module R M] [IsScalarTower k R M]

theorem mem_homogeneousCore_span_finiteHomogeneousComponents (i : Fin n) :
    x i ∈ homogeneousCore k M G
      ((Submodule.span R (finiteHomogeneousComponents k M G n x : Set M)).restrictScalars k) := by
  apply mem_homogeneousCore_of_components_mem
  intro q
  rcases component_mem_finiteHomogeneousComponents_or_zero k M G n x i q with hx | hx
  · exact Submodule.subset_span hx
  · rw [hx]
    exact Submodule.zero_mem _

end ASGinzburg
