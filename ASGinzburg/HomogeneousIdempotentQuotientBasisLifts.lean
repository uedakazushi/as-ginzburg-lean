import ASGinzburg.OrthogonalIdempotentGradedBasis
import ASGinzburg.HomogeneousIdempotentLifts
import ASGinzburg.HomogeneousOrdinaryQuotientDecomposition

/-! An actual homogeneous ordinary quotient has a genuine top basis with
homogeneous idempotent-fixed lifts. Every chosen generator degree retains
any lower bound of the original grading. -/
namespace ASGinzburg
open scoped DirectSum
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
variable (G : ℤ → Submodule k M) [DirectSum.Decomposition G] (S : Submodule R M)
variable {ι : Type z} [Fintype ι] [DecidableEq ι]
variable (e : ι → R) (he : ∀ i, e i*e i=e i)
variable (horth : ∀ i j, i≠j → e i*e j=0) (hsum : ∑ i, e i=1)

include he horth hsum in
theorem exists_homogeneous_idempotent_quotient_basis_lifts
    (hS : ∀ q x, x ∈ S.restrictScalars k →
      (DirectSum.decompose G x q : M) ∈ S.restrictScalars k)
    (heG : ∀ i q, ∀ x : M, x ∈ G q → e i • x ∈ G q)
    (b : ℤ) (hb : ∀ q, q < b → G q=⊥) :
    ∃ (γ : Type (max w z)) (c : γ → ι) (t : γ → ℤ)
      (B : Module.Basis γ k (M ⧸ S)) (x : γ → M),
      (∀ a, x a ∈ G (t a) ∧ e (c a) • x a=x a ∧ S.mkQ (x a)=B a) ∧
        (∀ a, b ≤ t a) := by
  classical
  let H := homogeneousOrdinaryQuotientGrade k R M G S
  letI : DirectSum.Decomposition H := homogeneousOrdinaryQuotientDecomposition k R M G S hS
  have hTop : ∀ i q, ∀ y : M ⧸ S, y ∈ H q → e i • y ∈ H q := by
    intro i q y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨e i • x, heG i q x hx, S.mkQ.map_smul (e i) x⟩
  let γ := idempotentHomogeneousBasisIndex k R (M ⧸ S) e H
  let B := idempotentHomogeneousBasis k R (M ⧸ S) e he horth hsum H hTop
  have hLift : ∀ a : γ, ∃ x : M,
      x ∈ G a.2.1 ∧ e a.1 • x=x ∧ S.mkQ x=B a := by
    intro a
    exact exists_homogeneous_idempotent_fixed_lift k R M (M ⧸ S) G S.mkQ
      (e a.1) (he a.1) (heG a.1) a.2.1 (B a)
      (idempotentHomogeneousBasis_mem_grade k R (M ⧸ S) e he horth hsum H hTop a)
      (idempotentHomogeneousBasis_fixed k R (M ⧸ S) e he horth hsum H hTop a)
  choose x hx using hLift
  refine ⟨γ, (fun a => a.1), (fun a => a.2.1), B, x, hx, ?_⟩
  intro a
  by_contra hba
  have hdeg : a.2.1 < b := lt_of_not_ge hba
  have hx0 : x a=0 := by simpa only [hb a.2.1 hdeg, Submodule.mem_bot] using (hx a).1
  have hBa : B a=0 := by rw [← (hx a).2.2, hx0, map_zero]
  exact (B.ne_zero a) hBa

end ASGinzburg
