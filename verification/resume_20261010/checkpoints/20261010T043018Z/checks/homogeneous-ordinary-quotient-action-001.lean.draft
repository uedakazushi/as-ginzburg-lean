import work.ASGinzburgDraft.HomogeneousOrdinaryQuotientDecomposition

/-! The genuine ordinary quotient action inherits the graded action of
the source module. In particular every degree-zero ring element preserves
each actual quotient grade. -/
namespace ASGinzburg
universe u v w
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module R M]
variable [IsScalarTower k R M]
variable (A : ℤ → Submodule k R) (G : ℤ → Submodule k M) (S : Submodule R M)

theorem homogeneousOrdinaryQuotientGrade_smul_mem
    (hAct : ∀ p q : ℤ, ∀ r ∈ A p, ∀ y ∈ G q, r • y ∈ G (p + q))
    (p q : ℤ) (r : R) (hr : r ∈ A p) (x : M ⧸ S)
    (hx : x ∈ homogeneousOrdinaryQuotientGrade k R M G S q) :
    r • x ∈ homogeneousOrdinaryQuotientGrade k R M G S (p + q) := by
  obtain ⟨y, hy, rfl⟩ := homogeneousOrdinaryQuotientGrade_exists_lift k R M G S q x hx
  have h := homogeneousOrdinaryQuotientGrade_mkQ_mem k R M G S (p + q)
    (r • y) (hAct p q r hr y hy)
  simpa only [map_smul] using h

theorem homogeneousOrdinaryQuotientGrade_zero_smul_mem
    (hAct : ∀ p q : ℤ, ∀ r ∈ A p, ∀ y ∈ G q, r • y ∈ G (p + q))
    (q : ℤ) (r : R) (hr : r ∈ A 0) (x : M ⧸ S)
    (hx : x ∈ homogeneousOrdinaryQuotientGrade k R M G S q) :
    r • x ∈ homogeneousOrdinaryQuotientGrade k R M G S q := by
  simpa only [zero_add] using
    homogeneousOrdinaryQuotientGrade_smul_mem k R M A G S hAct 0 q r hr x hx

theorem homogeneousOrdinaryQuotientGrade_degreeZero_action
    (hAct : ∀ p q : ℤ, ∀ r ∈ A p, ∀ y ∈ G q, r • y ∈ G (p + q))
    (r : R) (hr : r ∈ A 0) :
    ∀ q : ℤ, ∀ x : M ⧸ S, x ∈ homogeneousOrdinaryQuotientGrade k R M G S q →
      r • x ∈ homogeneousOrdinaryQuotientGrade k R M G S q :=
  fun q x hx => homogeneousOrdinaryQuotientGrade_zero_smul_mem k R M A G S hAct q r hr x hx

end ASGinzburg
