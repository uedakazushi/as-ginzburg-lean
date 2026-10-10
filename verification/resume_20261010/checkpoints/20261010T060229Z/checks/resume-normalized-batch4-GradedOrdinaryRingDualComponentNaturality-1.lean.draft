import ASGinzburg.GradedOrdinaryRingDualComponents

/-! Actual degree components of ring-linear dual maps commute with
actual precomposition by every degree-preserving ordinary module map. -/
namespace ASGinzburg.GradedOrdinaryModuleData
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]
variable {G : ℤ → Submodule k R} [DirectSum.Decomposition G]
variable (M N : GradedOrdinaryModuleData k R G)
variable (hG : ∀ p q : ℤ, ∀ a ∈ G p, ∀ b ∈ G q, a * b ∈ G (p + q))

theorem ringDualComponent_precomp (f : M.ringModule ⟶ N.ringModule)
    (hf : M.PreservesGrade N f) (g : ordinaryRingDual R N.ringModule) (q : ℤ) :
    ordinaryRingDualMap R f (N.ringDualComponent hG g q) =
      M.ringDualComponent hG (ordinaryRingDualMap R f g) q := by
  letI := M.decomposition
  apply LinearMap.ext
  intro x
  induction x using DirectSum.Decomposition.inductionOn M.grade with
  | zero => simp only [map_zero]
  | @homogeneous p x =>
    rw [ordinaryRingDualMap_apply,
      N.ringDualComponent_apply_homogeneous hG g q p (f x) (hf p x x.property),
      M.ringDualComponent_apply_homogeneous hG (ordinaryRingDualMap R f g) q p x x.property]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end ASGinzburg.GradedOrdinaryModuleData
