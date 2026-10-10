import work.ASGinzburgDraft.HomogeneousIdempotentQuotientBasisLifts
import Mathlib.RingTheory.Finiteness.Cardinality

/-! The genuine homogeneous idempotent-fixed quotient basis has a finite
index whenever the actual ordinary quotient is finite-dimensional. -/
namespace ASGinzburg
open scoped DirectSum
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
variable (G : ℤ → Submodule k M) [DirectSum.Decomposition G] (S : Submodule R M)
variable [Module.Finite k (M ⧸ S)]
variable {ι : Type z} [Fintype ι] [DecidableEq ι]
variable (e : ι → R) (he : ∀ i, e i*e i=e i)
variable (horth : ∀ i j, i≠j → e i*e j=0) (hsum : ∑ i, e i=1)

include he horth hsum in
theorem exists_finite_homogeneous_idempotent_quotient_basis_lifts
    (hS : ∀ q x, x ∈ S.restrictScalars k →
      (DirectSum.decompose G x q : M) ∈ S.restrictScalars k)
    (heG : ∀ i q, ∀ x : M, x ∈ G q → e i • x ∈ G q)
    (b : ℤ) (hb : ∀ q, q < b → G q=⊥) :
    ∃ (γ : Type (max w z)) (c : γ → ι) (t : γ → ℤ)
      (B : Module.Basis γ k (M ⧸ S)) (x : γ → M),
      Finite γ ∧
      (∀ a, x a ∈ G (t a) ∧ e (c a) • x a=x a ∧ S.mkQ (x a)=B a) ∧
        (∀ a, b ≤ t a) := by
  obtain ⟨γ,c,t,B,x,hx,ht⟩ :=
    exists_homogeneous_idempotent_quotient_basis_lifts k R M G S e he horth hsum hS heG b hb
  exact ⟨γ,c,t,B,x,Module.Finite.finite_basis B,hx,ht⟩

end ASGinzburg
