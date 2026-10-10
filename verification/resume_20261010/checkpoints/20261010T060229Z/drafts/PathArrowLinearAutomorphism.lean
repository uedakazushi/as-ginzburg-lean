import work.ASGinzburgDraft.PathArrowLinearSpaces
import ASGinzburg.PathArrowSubstitutionCutGrading

/-! Genuine invertible changes of the actual length-one arrow spaces
extend to actual vertex- and cut-preserving path-algebra automorphisms. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]
variable (L : ∀ i j : Q.Vertex, Q.pathArrowComponent k i j ≃ₗ[k] Q.pathArrowComponent k i j)

noncomputable def pathArrowLinearExtension (i j : Q.Vertex) :
    Q.PathComponent k i j →ₗ[k] Q.PathComponent k i j :=
  (Q.pathArrowComponent k i j).subtype.comp ((L i j).toLinearMap.comp
    ((Q.pathArrowProjection k i j).codRestrict _ (Q.pathArrowProjection_mem k i j)))

theorem pathArrowLinearExtension_on_arrow (i j : Q.Vertex)
    (f : Q.pathArrowComponent k i j) :
    Q.pathArrowLinearExtension k L i j f.val = (L i j f).val := by
  have H : (Q.pathArrowProjection k i j).codRestrict _
      (Q.pathArrowProjection_mem k i j) f.val = f := by
    apply Subtype.ext
    exact Q.pathArrowProjection_on_arrow k i j f
  change (L i j ((Q.pathArrowProjection k i j).codRestrict _
    (Q.pathArrowProjection_mem k i j) f.val)).val = _
  rw [H]

noncomputable def pathLinearArrowReplacement : Q.PathArrowReplacement k :=
  fun a => (L (Q.source a) (Q.target a) (Q.pathArrowBasisElement k a)).val

theorem pathLinearArrowReplacement_mem_cut (a : Q.Arrow) :
    Q.pathLinearArrowReplacement k L a ∈
      Q.pathCutComponent k (Q.source a) (Q.target a) (Q.cutDegree a : ℤ) := by
  rw [← Q.endpointArrowCutDegree_arrow a]
  exact Q.pathArrowComponent_le_cut k _ _ (L _ _ (Q.pathArrowBasisElement k a)).property

theorem pathLinearArrowSubstitution_on_arrow (i j : Q.Vertex)
    (f : Q.pathArrowComponent k i j) :
    Q.pathArrowSubstitutionComponent k (Q.pathLinearArrowReplacement k L) i j f.val =
      (L i j f).val := by
  have hf := f.property
  change f.val ∈ Finsupp.supported k k _ at hf
  rw [Finsupp.supported_eq_span_single] at hf
  rw [← Q.pathArrowLinearExtension_on_arrow k L i j f]
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
        have H := Q.pathArrowSubstitution_arrow k (Q.pathLinearArrowReplacement k L) a
        change Q.pathArrowSubstitutionComponent k (Q.pathLinearArrowReplacement k L)
          (Q.source a) (Q.target a) (Q.pathArrowBasisElement k a).val =
            Q.pathArrowLinearExtension k L (Q.source a) (Q.target a)
              (Q.pathArrowBasisElement k a).val
        rw [Q.pathArrowLinearExtension_on_arrow]
        exact H
      | snoc p b hb => simp [Path.length] at hp
  | zero => simp
  | add f g hf hg ihf ihg => simp only [map_add,ihf,ihg]
  | smul c f hf ih => simp only [map_smul,ih]

theorem pathLinearArrowSubstitution_inverse_on_arrow (a : Q.Arrow) :
    Q.pathArrowSubstitutionComponent k (Q.pathLinearArrowReplacement k L)
      (Q.source a) (Q.target a)
      (Q.pathLinearArrowReplacement k (fun i j => (L i j).symm) a) =
        Q.pathIdentityArrowReplacement k a := by
  rw [pathLinearArrowReplacement,Q.pathLinearArrowSubstitution_on_arrow]
  rw [LinearEquiv.apply_symm_apply]
  rfl

noncomputable def pathArrowLinearAutomorphism : Q.VertexCutPathAutomorphism k :=
  Q.pathArrowSubstitutionVertexCutAutomorphism k
    (Q.pathLinearArrowReplacement k L) (Q.pathLinearArrowReplacement k (fun i j => (L i j).symm))
    (Q.pathLinearArrowReplacement_mem_cut k L)
    (Q.pathLinearArrowReplacement_mem_cut k (fun i j => (L i j).symm))
    (Q.pathLinearArrowSubstitution_inverse_on_arrow k L)
    (by
      intro a
      simpa only [LinearEquiv.symm_symm] using
        Q.pathLinearArrowSubstitution_inverse_on_arrow k (fun i j => (L i j).symm) a)

end ASGinzburg.CutQuiver
