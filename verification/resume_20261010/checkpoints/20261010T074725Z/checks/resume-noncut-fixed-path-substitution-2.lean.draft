import ASGinzburg.PathArrowSubstitutionCutGrading

/-! Fixing every actual noncut arrow forces the free substitution to
fix every actual zero-cut path and linear combination of such paths. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]
variable (σ : Q.PathArrowReplacement k)
variable (hσ : ∀ a : Q.Arrow, Q.cut a = false → σ a = Q.pathIdentityArrowReplacement k a)

include hσ in
theorem pathArrowSubstitutionPath_eq_self_of_noncut_fixed
    {i j : Q.Vertex} (p : Q.Path i j) (hp : p.cutDegree = 0) :
    Q.pathArrowSubstitutionPath k σ p = Finsupp.single p 1 := by
  induction p with
  | nil => simp only [pathArrowSubstitutionPath, pathId]
  | @snoc j p a ha ih =>
    have hc : Q.cut a = false := by
      cases H : Q.cut a
      · rfl
      · simp only [Path.cutDegree, Q.cutDegree_true H] at hp
        omega
    have hpc : p.cutDegree = 0 := by
      simpa only [Path.cutDegree, Q.cutDegree_false hc, Nat.add_zero] using hp
    subst j
    rw [pathArrowSubstitutionPath, hσ a hc, ih hpc]
    simp only [pathIdentityArrowReplacement, Q.pathComp_single, one_mul, Path.comp]

include hσ in
theorem pathArrowSubstitutionComponent_eq_self_of_noncut_fixed
    (i j : Q.Vertex) (f : Q.pathCutComponent k i j 0) :
    Q.pathArrowSubstitutionComponent k σ i j f.val = f.val := by
  have hf := f.property
  change f.val ∈ Finsupp.supported k k _ at hf
  rw [Finsupp.supported_eq_span_single] at hf
  generalize f.val = x at hf ⊢
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    have hc : p.cutDegree = 0 := by exact_mod_cast hp
    rw [Q.pathArrowSubstitutionComponent_single, one_smul,
      Q.pathArrowSubstitutionPath_eq_self_of_noncut_fixed k σ hσ p hc]
  | zero => exact map_zero _
  | add f g hf hg ihf ihg => exact map_add _ _ _ |>.trans (congrArg₂ (· + ·) ihf ihg)
  | smul c f hf ih => exact map_smul _ _ _ |>.trans (congrArg (c • ·) ih)

end ASGinzburg.CutQuiver
