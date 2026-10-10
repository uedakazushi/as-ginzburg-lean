import ASGinzburg.HomogeneousQuotientDecomposition

/-! An actual quotient by an ordinary ring submodule inherits the genuine
homogeneous decomposition and lower bound of a compatibly graded module.
Each quotient grade is the actual image of the homogeneous source grade. -/
namespace ASGinzburg
open scoped DirectSum
universe u v w
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module R M]
variable [IsScalarTower k R M]
variable (G : ℤ → Submodule k M) [DirectSum.Decomposition G]
variable (S : Submodule R M)

def homogeneousOrdinaryQuotientGrade (q : ℤ) : Submodule k (M ⧸ S) :=
  (G q).map (S.mkQ.restrictScalars k)

def homogeneousOrdinaryQuotientScalarsEquiv :
    (M ⧸ S.restrictScalars k) ≃ₗ[k] (M ⧸ S) :=
  Submodule.Quotient.restrictScalarsEquiv k S

@[simp] theorem homogeneousOrdinaryQuotientScalarsEquiv_mkQ (x : M) :
    homogeneousOrdinaryQuotientScalarsEquiv k R M S
      ((S.restrictScalars k).mkQ x) = S.mkQ x := rfl

noncomputable def homogeneousOrdinaryQuotientDecomposition
    (hS : ∀ (q : ℤ) (x : M), x ∈ S.restrictScalars k →
      (DirectSum.decompose G x q : M) ∈ S.restrictScalars k) :
    DirectSum.Decomposition (homogeneousOrdinaryQuotientGrade k R M G S) := by
  letI := homogeneousQuotientDecomposition k M G (S.restrictScalars k) hS
  exact {
    decompose' := DirectSum.decompose (homogeneousQuotientGrade k M G (S.restrictScalars k))
    left_inv := (DirectSum.decompose (homogeneousQuotientGrade k M G (S.restrictScalars k))).left_inv
    right_inv := (DirectSum.decompose (homogeneousQuotientGrade k M G (S.restrictScalars k))).right_inv
  }

omit [DirectSum.Decomposition G] in
theorem homogeneousOrdinaryQuotientGrade_exists_lift (q : ℤ) (x : M ⧸ S)
    (hx : x ∈ homogeneousOrdinaryQuotientGrade k R M G S q) :
    ∃ y : M, y ∈ G q ∧ S.mkQ y = x := hx

omit [DirectSum.Decomposition G] in
theorem homogeneousOrdinaryQuotientGrade_mkQ_mem (q : ℤ) (x : M) (hx : x ∈ G q) :
    S.mkQ x ∈ homogeneousOrdinaryQuotientGrade k R M G S q := ⟨x, hx, rfl⟩

omit [DirectSum.Decomposition G] in
theorem homogeneousOrdinaryQuotientGrade_eq_bot_of_lower_bound
    (b : ℤ) (hb : ∀ q : ℤ, q < b → G q = ⊥) (q : ℤ) (hq : q < b) :
    homogeneousOrdinaryQuotientGrade k R M G S q = ⊥ := by
  rw [homogeneousOrdinaryQuotientGrade, hb q hq, Submodule.map_bot]

end ASGinzburg
