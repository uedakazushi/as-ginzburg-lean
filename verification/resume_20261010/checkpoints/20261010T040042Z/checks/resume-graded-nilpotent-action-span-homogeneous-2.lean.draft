import ASGinzburg.GradedNilpotentNakayama
import work.ASGinzburgDraft.ScalarStableGradedDecomposition

/-! The genuine nilpotent-degree-zero/positive-operator action span is
homogeneous. Therefore the actual radical top inherits the internal
grading; no extra top grading is assumed. -/
namespace ASGinzburg
open scoped DirectSum
universe u v w z
variable (k : Type u) [Field k] (R₀ : Type v) [Ring R₀] [Algebra k R₀]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module R₀ M]
  [IsScalarTower k R₀ M]
variable (G : ℤ → Submodule R₀ M) [DirectSum.Decomposition G]

noncomputable def gradedModuleComponentProjection (q : ℤ) : M →ₗ[R₀] M :=
  (G q).subtype.comp (gradedZeroComponent R₀ M G q)

variable {ι : Type z} (d : ι → ℕ) (f : ι → M →ₗ[k] M) (I₀ : Ideal R₀)

omit [Algebra k R₀] [IsScalarTower k R₀ M] in
theorem gradedNilpotentActionSpan_projection_positive (q : ℤ) (t : ι)
    (hf : ∀ (p : ℤ) (x : M), x ∈ G p → f t x ∈ G (p+(d t:ℤ))) :
    ∀ x : M, gradedModuleComponentProjection R₀ M G q (f t x) ∈
      gradedNilpotentActionSpan k R₀ M f I₀ := by
  intro x
  induction x using DirectSum.Decomposition.inductionOn G with
  | zero => rw [map_zero, map_zero]; exact Submodule.zero_mem _
  | @homogeneous p x =>
    by_cases h : p+(d t:ℤ) = q
    · have hx : f t x ∈ G q := h ▸ hf p x x.property
      have he : gradedModuleComponentProjection R₀ M G q (f t x) = f t x :=
        DirectSum.decompose_of_mem_same G hx
      rw [he]
      exact Submodule.subset_span (Or.inr ⟨t,x,rfl⟩)
    · have he : gradedModuleComponentProjection R₀ M G q (f t x) = 0 :=
        DirectSum.decompose_of_mem_ne G (hf p x x.property) h
      rw [he]
      exact Submodule.zero_mem _
  | add x y hx hy =>
    rw [map_add, map_add]
    exact Submodule.add_mem _ hx hy

theorem gradedNilpotentActionSpan_homogeneous
    (hf : ∀ (t : ι) (p : ℤ) (x : M), x ∈ G p → f t x ∈ G (p+(d t:ℤ))) :
    DirectSum.SetLike.IsHomogeneous G (gradedNilpotentActionSpan k R₀ M f I₀) := by
  intro q x hx
  change gradedModuleComponentProjection R₀ M G q x ∈ _
  unfold gradedNilpotentActionSpan at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · obtain ⟨r,hr,y,rfl⟩ := hy
      rw [map_smul]
      exact Submodule.subset_span (Or.inl
        ⟨r,hr,gradedModuleComponentProjection R₀ M G q y,rfl⟩)
    · obtain ⟨t,y,rfl⟩ := hy
      exact gradedNilpotentActionSpan_projection_positive k R₀ M G d f I₀ q t (hf t) y
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul c x hx ihx =>
    change ((gradedModuleComponentProjection R₀ M G q).restrictScalars k) (c • x) ∈ _
    rw [map_smul]
    exact Submodule.smul_mem _ c ihx

variable (H : ℤ → Submodule k M) [DirectSum.Decomposition H]
variable (h₀ : ∀ (q : ℤ) (r : R₀) (x : M), x ∈ H q → r • x ∈ H q)

include h₀ in
omit [DirectSum.Decomposition G] in
theorem gradedNilpotentActionSpan_linear_homogeneous
    (hf : ∀ (t : ι) (p : ℤ) (x : M), x ∈ H p → f t x ∈ H (p+(d t:ℤ))) :
    DirectSum.SetLike.IsHomogeneous H (gradedNilpotentActionSpan k R₀ M f I₀) := by
  let G₀ := scalarStableGrade k R₀ M H h₀
  letI : DirectSum.Decomposition G₀ := scalarStableGradeDecomposition k R₀ M H h₀
  exact gradedNilpotentActionSpan_homogeneous k R₀ M G₀ d f I₀ hf

end ASGinzburg
