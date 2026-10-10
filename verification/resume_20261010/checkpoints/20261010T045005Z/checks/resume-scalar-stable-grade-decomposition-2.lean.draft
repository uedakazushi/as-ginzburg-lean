import Mathlib.Algebra.DirectSum.Decomposition

/-! A grading by scalar-stable vector subspaces is a grading by actual
submodules over the larger scalar ring. Its direct-sum decomposition and
lower bound are preserved without changing the underlying subspaces. -/
namespace ASGinzburg
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module R M]
variable {ι : Type z} [DecidableEq ι] (G : ι → Submodule k M)
variable (hG : ∀ (q : ι) (r : R) (x : M), x ∈ G q → r • x ∈ G q)

def scalarStableGrade (q : ι) : Submodule R M where
  carrier := G q
  zero_mem' := (G q).zero_mem
  add_mem' := (G q).add_mem
  smul_mem' := hG q

omit [DecidableEq ι] in
theorem mem_scalarStableGrade (q : ι) (x : M) :
    x ∈ scalarStableGrade k R M G hG q ↔ x ∈ G q := Iff.rfl

noncomputable def scalarStableGradeDecomposition [DirectSum.Decomposition G] :
    DirectSum.Decomposition (scalarStableGrade k R M G hG) where
  decompose' := DirectSum.decompose G
  left_inv := (DirectSum.decompose G).left_inv
  right_inv := (DirectSum.decompose G).right_inv

omit [DecidableEq ι] in
theorem scalarStableGrade_eq_bot_of_eq_bot (q : ι) (hq : G q = ⊥) :
    scalarStableGrade k R M G hG q = ⊥ := by
  ext x
  change x ∈ G q ↔ x = 0
  rw [hq]
  rfl

end ASGinzburg
