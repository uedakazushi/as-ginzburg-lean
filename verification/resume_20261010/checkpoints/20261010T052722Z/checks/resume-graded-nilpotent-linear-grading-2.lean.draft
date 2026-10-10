import work.ASGinzburgDraft.GradedNilpotentNakayama
import work.ASGinzburgDraft.ScalarStableGradedDecomposition

/-! The genuine bounded-below graded Nakayama criterion accepts an ordinary
k-linear internal grading that is invariant under the actual degree-zero
ring action. The degree-zero submodule structure and decomposition are
constructed from that invariance. -/
namespace ASGinzburg
open scoped DirectSum
universe u v w z
variable (k : Type u) [Field k] (R₀ : Type v) [Ring R₀] [Algebra k R₀]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module R₀ M] [IsScalarTower k R₀ M]
variable (G : ℤ → Submodule k M) [DirectSum.Decomposition G]
variable (h₀ : ∀ (q : ℤ) (r : R₀) (x : M), x ∈ G q → r • x ∈ G q)

variable {ι : Type z} (d : ι → ℕ) (f : ι → M →ₗ[k] M) (I₀ : Ideal R₀)

include h₀ in
theorem gradedModule_subsingleton_of_linear_grading_nilpotent_action_span_top
    (N : ℕ) (hN : I₀^N = ⊥) (hd : ∀ t : ι, 0 < d t)
    (hf : ∀ (t : ι) (p : ℤ) (x : M), x ∈ G p → f t x ∈ G (p+(d t:ℤ)))
    (b : ℤ) (hb : ∀ p : ℤ, p < b → G p = ⊥)
    (hRad : gradedNilpotentActionSpan k R₀ M f I₀ = ⊤) :
    Subsingleton M := by
  let G₀ := scalarStableGrade k R₀ M G h₀
  letI : DirectSum.Decomposition G₀ := scalarStableGradeDecomposition k R₀ M G h₀
  exact gradedModule_subsingleton_of_boundedBelow_nilpotent_action_span_top k R₀ M G₀
    d f I₀ N hN hd hf b
    (fun p hp => scalarStableGrade_eq_bot_of_eq_bot k R₀ M G h₀ p (hb p hp)) hRad

end ASGinzburg
