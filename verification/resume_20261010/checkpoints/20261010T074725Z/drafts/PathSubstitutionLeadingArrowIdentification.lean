import work.ASGinzburgDraft.PathArrowLinearAutomorphism

/-! Equality on genuine leading arrow images determines the entire
actual leading component map. A genuine linear change then proves its
bijectivity on every arrow space. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]
variable (σ : Q.PathArrowReplacement k)
variable (L : ∀ i j : Q.Vertex, Q.pathArrowComponent k i j ≃ₗ[k] Q.pathArrowComponent k i j)
variable (h : ∀ a : Q.Arrow, Q.pathArrowProjection k (Q.source a) (Q.target a) (σ a) =
  (L (Q.source a) (Q.target a) (Q.pathArrowBasisElement k a)).val)

include h in
theorem pathSubstitutionArrowLinearMap_eq_of_arrow_images (i j : Q.Vertex) :
    Q.pathSubstitutionArrowLinearMap k σ i j = (L i j).toLinearMap := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  change Q.pathArrowProjection k i j (Q.pathArrowSubstitutionComponent k σ i j f.val) =
    (L i j f).val
  rw [← Q.pathArrowLinearExtension_on_arrow k L i j f]
  have hf := f.property
  change f.val ∈ Finsupp.supported k k _ at hf
  rw [Finsupp.supported_eq_span_single] at hf
  generalize f.val = x at hf ⊢
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    change p.length = 1 at hp
    cases p with
    | nil => simp [Path.length] at hp
    | @snoc j p a ha =>
      cases p with
      | nil =>
        subst i
        rw [Q.pathArrowSubstitution_arrow]
        change Q.pathArrowProjection k (Q.source a) (Q.target a) (σ a) =
          Q.pathArrowLinearExtension k L (Q.source a) (Q.target a)
            (Q.pathArrowBasisElement k a).val
        rw [Q.pathArrowLinearExtension_on_arrow]
        exact h a
      | snoc p b hb => simp [Path.length] at hp
  | zero => simp
  | add f g hf hg ihf ihg => simp only [map_add, ihf, ihg]
  | smul c f hf ih => simp only [map_smul, ih]

include h in
theorem pathSubstitutionArrowLinearMap_bijective_of_arrow_images (i j : Q.Vertex) :
    Function.Bijective (Q.pathSubstitutionArrowLinearMap k σ i j) := by
  rw [Q.pathSubstitutionArrowLinearMap_eq_of_arrow_images k σ L h i j]
  exact (L i j).bijective

end ASGinzburg.CutQuiver
