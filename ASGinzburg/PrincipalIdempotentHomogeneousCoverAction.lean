import ASGinzburg.PrincipalIdempotentHomogeneousCover

/-! The actual ordinary ring action on a direct sum of shifted principal
modules is graded for the constructed homogeneous cover grading. -/
namespace ASGinzburg
open scoped DirectSum ModuleCat.Algebra
universe u v w
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (G : ℤ → Submodule k R)
variable {γ : Type w} (e : γ → R) (t : γ → ℤ)

theorem principalHomogeneousCoverGrade_smul_mem
    (hMul : ∀ p q : ℤ, ∀ r ∈ G p, ∀ s ∈ G q, r * s ∈ G (p + q))
    (p q : ℤ) (r : R) (hr : r ∈ G p)
    (x : ⨁ a, principalIdempotentModule R (e a))
    (hx : x ∈ principalHomogeneousCoverGrade k R G e t q) :
    r • x ∈ principalHomogeneousCoverGrade k R G e t (p + q) := by
  rw [principalHomogeneousCoverGrade_mem_iff k R G e t] at hx ⊢
  intro a
  change r * (x a).val ∈ G (p + q - t a)
  have h := hMul p (q - t a) r hr (x a).val (hx a)
  have hdegree : p + (q - t a) = p + q - t a := by omega
  simpa only [hdegree] using h

theorem principalHomogeneousCoverGrade_zero_smul_mem
    (hMul : ∀ p q : ℤ, ∀ r ∈ G p, ∀ s ∈ G q, r * s ∈ G (p + q))
    (q : ℤ) (r : R) (hr : r ∈ G 0)
    (x : ⨁ a, principalIdempotentModule R (e a))
    (hx : x ∈ principalHomogeneousCoverGrade k R G e t q) :
    r • x ∈ principalHomogeneousCoverGrade k R G e t q := by
  simpa only [zero_add] using
    principalHomogeneousCoverGrade_smul_mem k R G e t hMul 0 q r hr x hx

end ASGinzburg
