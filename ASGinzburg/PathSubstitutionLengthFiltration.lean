import ASGinzburg.PathArrowSubstitutionInverse
import ASGinzburg.PathAutomorphismLengthFiltration

/-! Actual arrow substitutions preserve path length, and a substitution
whose leading arrow part is the identity raises length after subtraction. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem pathArrowSubstitutionPath_mem_length (σ : Q.PathArrowReplacement k)
    {i j : Q.Vertex} (p : Q.Path i j) :
    Q.pathArrowSubstitutionPath k σ p ∈ Q.pathLengthFiltration k p.length i j := by
  induction p with
  | nil => exact Q.mem_pathLengthFiltration_zero k _
  | @snoc j p a ha ih =>
    subst j
    rw [pathArrowSubstitutionPath]
    exact Q.pathComp_mem_lengthFiltration k ih
      (Q.pathLengthFiltration_one_mem_of_ne k (Q.pathAutomorphism_arrow_source_ne_target a) _)

theorem pathArrowSubstitutionComponent_mem_length (σ : Q.PathArrowReplacement k)
    (n : ℕ) {i j : Q.Vertex} (f : Q.PathComponent k i j)
    (hf : f ∈ Q.pathLengthFiltration k n i j) :
    Q.pathArrowSubstitutionComponent k σ i j f ∈ Q.pathLengthFiltration k n i j := by
  change f ∈ Finsupp.supported k k _ at hf
  rw [Finsupp.supported_eq_span_single] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p,hp,rfl⟩ := hx
    rw [pathArrowSubstitutionComponent_single,one_smul]
    exact Q.pathLengthFiltration_le_of_le k hp i j
      (Q.pathArrowSubstitutionPath_mem_length k σ p)
  | zero => simp
  | add f g hf hg ihf ihg => simpa only [map_add] using Submodule.add_mem _ ihf ihg
  | smul c f hf ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

theorem pathArrowSubstitutionPath_sub_identity_mem_length
    (σ : Q.PathArrowReplacement k)
    (hσ : ∀ a, σ a - Q.pathIdentityArrowReplacement k a ∈
      Q.pathLengthFiltration k 2 (Q.source a) (Q.target a))
    {i j : Q.Vertex} (p : Q.Path i j) :
    Q.pathArrowSubstitutionPath k σ p - Finsupp.single p 1 ∈
      Q.pathLengthFiltration k (p.length + 1) i j := by
  induction p with
  | nil => simp [pathArrowSubstitutionPath,pathId]
  | @snoc j p a ha ih =>
    subst j
    have hp : Q.pathComp k (Q.pathIdentityArrowReplacement k a)
        (Finsupp.single p 1) = Finsupp.single (Path.snoc p a rfl) 1 := by
      simp [pathIdentityArrowReplacement,pathComp_single,Path.comp]
    have H : Q.pathComp k (σ a) (Q.pathArrowSubstitutionPath k σ p) -
        Q.pathComp k (Q.pathIdentityArrowReplacement k a) (Finsupp.single p 1) =
      Q.pathComp k (σ a - Q.pathIdentityArrowReplacement k a)
        (Q.pathArrowSubstitutionPath k σ p) +
      Q.pathComp k (Q.pathIdentityArrowReplacement k a)
        (Q.pathArrowSubstitutionPath k σ p - Finsupp.single p 1) := by
      simp only [map_sub,LinearMap.sub_apply]
      abel
    rw [pathArrowSubstitutionPath,← hp,H]
    apply Submodule.add_mem
    · simpa only [Path.length,Nat.add_assoc] using
        Q.pathComp_mem_lengthFiltration k
          (Q.pathArrowSubstitutionPath_mem_length k σ p) (hσ a)
    · have ha : Q.pathIdentityArrowReplacement k a ∈
          Q.pathLengthFiltration k 1 (Q.source a) (Q.target a) :=
        Q.pathLengthFiltration_one_mem_of_ne k (Q.pathAutomorphism_arrow_source_ne_target a) _
      exact Q.pathComp_mem_lengthFiltration k ih ha

noncomputable def pathSubstitutionDifference (σ : Q.PathArrowReplacement k) (i j : Q.Vertex) :
    Module.End k (Q.PathComponent k i j) :=
  Q.pathArrowSubstitutionComponent k σ i j - LinearMap.id

theorem pathSubstitutionDifference_mem_length (σ : Q.PathArrowReplacement k)
    (hσ : ∀ a, σ a - Q.pathIdentityArrowReplacement k a ∈
      Q.pathLengthFiltration k 2 (Q.source a) (Q.target a))
    (n : ℕ) {i j : Q.Vertex} (f : Q.PathComponent k i j)
    (hf : f ∈ Q.pathLengthFiltration k n i j) :
    Q.pathSubstitutionDifference k σ i j f ∈ Q.pathLengthFiltration k (n+1) i j := by
  change f ∈ Finsupp.supported k k _ at hf
  rw [Finsupp.supported_eq_span_single] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p,hp,rfl⟩ := hx
    change Q.pathArrowSubstitutionComponent k σ i j (Finsupp.single p 1) -
      Finsupp.single p 1 ∈ _
    rw [pathArrowSubstitutionComponent_single,one_smul]
    exact Q.pathLengthFiltration_le_of_le k (Nat.add_le_add_right hp 1) i j
      (Q.pathArrowSubstitutionPath_sub_identity_mem_length k σ hσ p)
  | zero => simp
  | add f g hf hg ihf ihg => simpa only [map_add] using Submodule.add_mem _ ihf ihg
  | smul c f hf ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

end ASGinzburg.CutQuiver
