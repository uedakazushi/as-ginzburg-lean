import work.ASGinzburgDraft.PathArrowLinearSpaces
import ASGinzburg.PathSubstitutionLengthFiltration

/-! The actual leading-arrow projection annihilates decomposable paths.
Consequently leading maps of substitutions compose on genuine arrows. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem pathArrowProjection_eq_zero_of_length_two {i j : Q.Vertex}
    (f : Q.PathComponent k i j) (hf : f ∈ Q.pathLengthFiltration k 2 i j) :
    Q.pathArrowProjection k i j f = 0 := by
  change f ∈ Finsupp.supported k k _ at hf
  rw [Finsupp.supported_eq_span_single] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p,hp,rfl⟩ := hx
    rw [Q.pathArrowProjection_single]
    exact if_neg (by change 2 ≤ p.length at hp; omega)
  | zero => exact map_zero _
  | add f g hf hg ihf ihg => simp only [map_add,ihf,ihg,add_zero]
  | smul c f hf ih => simp only [map_smul,ih,smul_zero]

theorem pathArrowProjection_substitution_projection (σ : Q.PathArrowReplacement k)
    (i j : Q.Vertex) (hij : i ≠ j) (f : Q.PathComponent k i j) :
    Q.pathArrowProjection k i j
      (Q.pathArrowSubstitutionComponent k σ i j (Q.pathArrowProjection k i j f)) =
      Q.pathArrowProjection k i j (Q.pathArrowSubstitutionComponent k σ i j f) := by
  have H := Q.pathArrowProjection_eq_zero_of_length_two k
    (Q.pathArrowSubstitutionComponent k σ i j (f - Q.pathArrowProjection k i j f))
    (Q.pathArrowSubstitutionComponent_mem_length k σ 2 _
      (Q.sub_pathArrowProjection_mem_length_two k i j hij f))
  rw [map_sub,map_sub] at H
  exact (sub_eq_zero.mp H).symm

theorem pathSubstitutionArrowLinearMap_comp_arrow (σ τ : Q.PathArrowReplacement k)
    (a : Q.Arrow) :
    (Q.pathSubstitutionArrowLinearMap k τ (Q.source a) (Q.target a)
      (Q.pathSubstitutionArrowLinearMap k σ (Q.source a) (Q.target a)
        (Q.pathArrowBasisElement k a))).val =
      Q.pathArrowProjection k (Q.source a) (Q.target a)
        (Q.pathArrowSubstitutionComponent k τ (Q.source a) (Q.target a) (σ a)) := by
  change Q.pathArrowProjection k _ _
    (Q.pathArrowSubstitutionComponent k τ _ _
      (Q.pathArrowProjection k _ _
        (Q.pathArrowSubstitutionComponent k σ _ _ (Q.pathIdentityArrowReplacement k a)))) = _
  rw [pathIdentityArrowReplacement,Q.pathArrowSubstitution_arrow]
  exact Q.pathArrowProjection_substitution_projection k τ _ _
    (Q.pathAutomorphism_arrow_source_ne_target a) (σ a)

theorem pathSubstitutionArrowLinearMap_inverse_of_arrow (σ τ : Q.PathArrowReplacement k)
    (h : ∀ a, Q.pathArrowProjection k (Q.source a) (Q.target a)
      (Q.pathArrowSubstitutionComponent k τ (Q.source a) (Q.target a) (σ a)) =
        Q.pathIdentityArrowReplacement k a)
    (i j : Q.Vertex) (f : Q.pathArrowComponent k i j) :
    Q.pathSubstitutionArrowLinearMap k τ i j (Q.pathSubstitutionArrowLinearMap k σ i j f) = f := by
  have hf := f.property
  change f.val ∈ Finsupp.supported k k _ at hf
  rw [Finsupp.supported_eq_span_single] at hf
  apply Subtype.ext
  change Q.pathArrowProjection k i j (Q.pathArrowSubstitutionComponent k τ i j
    (Q.pathArrowProjection k i j (Q.pathArrowSubstitutionComponent k σ i j f.val))) = f.val
  generalize f.val = x at hf ⊢
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p,hp,rfl⟩ := hx
    change p.length = 1 at hp
    cases p with
    | nil => simp [Path.length] at hp
    | @snoc j p a ha =>
      cases p with
      | nil =>
        subst i
        exact (Q.pathSubstitutionArrowLinearMap_comp_arrow k σ τ a).trans (h a)
      | snoc => simp [Path.length] at hp
  | zero => simp
  | add f g hf hg ihf ihg =>
    simp only [map_add,ihf,ihg]
  | smul c f hf ih => simp only [map_smul,ih]

end ASGinzburg.CutQuiver
