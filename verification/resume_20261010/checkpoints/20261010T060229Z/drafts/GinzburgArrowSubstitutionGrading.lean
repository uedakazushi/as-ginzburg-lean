import work.ASGinzburgDraft.GinzburgArrowSubstitutionInverse
import ASGinzburg.GinzburgCutCochainComplex
import ASGinzburg.GinzburgSupportedProducts

/-! Actual homogeneous generator replacements preserve the actual path
gradings, so inverse substitutions restrict to graded component equivalences. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgArrowSubstitutionPath_mem_cohomological
    (σ : Q.GinzburgArrowReplacement k)
    (hσ : ∀ a, σ a ∈ Q.ginzburgCohomologicalComponent k (a.source Q) (a.target Q)
      (a.cohomologicalDegree Q)) {i j : Q.Vertex} (p : Q.GinzburgPath i j) :
    Q.ginzburgArrowSubstitutionPath k σ p ∈
      Q.ginzburgCohomologicalComponent k i j p.cohomologicalDegree := by
  induction p with
  | nil =>
    simp only [ginzburgArrowSubstitutionPath,GinzburgPath.cohomologicalDegree,ginzburgPathId]
    exact Finsupp.single_mem_supported k 1 rfl
  | @snoc j p a h ih =>
    subst j
    rw [ginzburgArrowSubstitutionPath]
    exact Q.ginzburgCohomologicalComponent_comp k ih (hσ a)

theorem ginzburgArrowSubstitutionComponent_mem_cohomological
    (σ : Q.GinzburgArrowReplacement k)
    (hσ : ∀ a, σ a ∈ Q.ginzburgCohomologicalComponent k (a.source Q) (a.target Q)
      (a.cohomologicalDegree Q)) (i j : Q.Vertex) (q : ℤ)
    (f : Q.GinzburgPathComponent k i j) (hf : f ∈ Q.ginzburgCohomologicalComponent k i j q) :
    Q.ginzburgArrowSubstitutionComponent k σ i j f ∈
      Q.ginzburgCohomologicalComponent k i j q := by
  change f ∈ Finsupp.supported k k _ at hf
  rw [Finsupp.supported_eq_span_single] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p,hp,rfl⟩ := hx
    rw [Q.ginzburgArrowSubstitutionComponent_single,one_smul]
    change p.cohomologicalDegree=q at hp
    rw [← hp]
    exact Q.ginzburgArrowSubstitutionPath_mem_cohomological k σ hσ p
  | zero => simpa only [map_zero] using (Q.ginzburgCohomologicalComponent k i j q).zero_mem
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using (Q.ginzburgCohomologicalComponent k i j q).add_mem ihx ihy
  | smul a x hx ih =>
    simpa only [map_smul] using (Q.ginzburgCohomologicalComponent k i j q).smul_mem a ih

theorem ginzburgArrowSubstitutionPath_mem_cut
    (σ : Q.GinzburgArrowReplacement k)
    (hσ : ∀ a, σ a ∈ Q.ginzburgCutComponent k (a.source Q) (a.target Q) (a.cutDegree Q))
    {i j : Q.Vertex} (p : Q.GinzburgPath i j) :
    Q.ginzburgArrowSubstitutionPath k σ p ∈ Q.ginzburgCutComponent k i j p.cutDegree := by
  induction p with
  | nil =>
    simp only [ginzburgArrowSubstitutionPath,GinzburgPath.cutDegree,ginzburgPathId]
    exact Finsupp.single_mem_supported k 1 rfl
  | @snoc j p a h ih =>
    subst j
    rw [ginzburgArrowSubstitutionPath]
    exact Q.ginzburgCutComponent_comp k ih (hσ a)

theorem ginzburgArrowSubstitutionComponent_mem_cut
    (σ : Q.GinzburgArrowReplacement k)
    (hσ : ∀ a, σ a ∈ Q.ginzburgCutComponent k (a.source Q) (a.target Q) (a.cutDegree Q))
    (i j : Q.Vertex) (c : ℤ) (f : Q.GinzburgPathComponent k i j)
    (hf : f ∈ Q.ginzburgCutComponent k i j c) :
    Q.ginzburgArrowSubstitutionComponent k σ i j f ∈ Q.ginzburgCutComponent k i j c := by
  change f ∈ Finsupp.supported k k _ at hf
  rw [Finsupp.supported_eq_span_single] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p,hp,rfl⟩ := hx
    rw [Q.ginzburgArrowSubstitutionComponent_single,one_smul]
    change p.cutDegree=c at hp
    rw [← hp]
    exact Q.ginzburgArrowSubstitutionPath_mem_cut k σ hσ p
  | zero => simpa only [map_zero] using (Q.ginzburgCutComponent k i j c).zero_mem
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using (Q.ginzburgCutComponent k i j c).add_mem ihx ihy
  | smul a x hx ih =>
    simpa only [map_smul] using (Q.ginzburgCutComponent k i j c).smul_mem a ih

theorem ginzburgArrowSubstitutionPath_mem_homogeneous
    (σ : Q.GinzburgArrowReplacement k)
    (hσ : ∀ a, σ a ∈ Q.ginzburgHomogeneousComponent k (a.source Q) (a.target Q)
      (a.cohomologicalDegree Q) (a.cutDegree Q) (a.winding Q))
    {i j : Q.Vertex} (p : Q.GinzburgPath i j) :
    Q.ginzburgArrowSubstitutionPath k σ p ∈
      Q.ginzburgHomogeneousComponent k i j p.cohomologicalDegree p.cutDegree p.winding := by
  induction p with
  | nil =>
    simp only [ginzburgArrowSubstitutionPath,GinzburgPath.cohomologicalDegree,
      GinzburgPath.cutDegree,GinzburgPath.winding,ginzburgPathId]
    exact Finsupp.single_mem_supported k 1 ⟨rfl,rfl,rfl⟩
  | @snoc j p a h ih =>
    subst j
    rw [ginzburgArrowSubstitutionPath]
    exact Q.ginzburgHomogeneousComponent_comp k ih (hσ a)

theorem ginzburgArrowSubstitutionComponent_mem_homogeneous
    (σ : Q.GinzburgArrowReplacement k)
    (hσ : ∀ a, σ a ∈ Q.ginzburgHomogeneousComponent k (a.source Q) (a.target Q)
      (a.cohomologicalDegree Q) (a.cutDegree Q) (a.winding Q))
    (i j : Q.Vertex) (q c w : ℤ) (f : Q.GinzburgPathComponent k i j)
    (hf : f ∈ Q.ginzburgHomogeneousComponent k i j q c w) :
    Q.ginzburgArrowSubstitutionComponent k σ i j f ∈
      Q.ginzburgHomogeneousComponent k i j q c w := by
  change f ∈ Finsupp.supported k k _ at hf
  rw [Finsupp.supported_eq_span_single] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p,hp,rfl⟩ := hx
    rw [Q.ginzburgArrowSubstitutionComponent_single,one_smul]
    change p.cohomologicalDegree=q ∧ p.cutDegree=c ∧ p.winding=w at hp
    rw [← hp.1,← hp.2.1,← hp.2.2]
    exact Q.ginzburgArrowSubstitutionPath_mem_homogeneous k σ hσ p
  | zero => simpa only [map_zero] using (Q.ginzburgHomogeneousComponent k i j q c w).zero_mem
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using (Q.ginzburgHomogeneousComponent k i j q c w).add_mem ihx ihy
  | smul a x hx ih =>
    simpa only [map_smul] using (Q.ginzburgHomogeneousComponent k i j q c w).smul_mem a ih

noncomputable def ginzburgArrowSubstitutionRestrictedEquiv
    (σ τ : Q.GinzburgArrowReplacement k)
    (hστ : ∀ a, Q.ginzburgArrowSubstitutionComponent k σ (a.source Q) (a.target Q) (τ a) =
      Q.ginzburgIdentityArrowReplacement k a)
    (hτσ : ∀ a, Q.ginzburgArrowSubstitutionComponent k τ (a.source Q) (a.target Q) (σ a) =
      Q.ginzburgIdentityArrowReplacement k a)
    (i j : Q.Vertex) (S : Submodule k (Q.GinzburgPathComponent k i j))
    (hσ : ∀ f ∈ S, Q.ginzburgArrowSubstitutionComponent k σ i j f ∈ S)
    (hτ : ∀ f ∈ S, Q.ginzburgArrowSubstitutionComponent k τ i j f ∈ S) : S ≃ₗ[k] S :=
  { toFun := fun f => ⟨Q.ginzburgArrowSubstitutionComponent k σ i j f.val,hσ f.val f.property⟩
    invFun := fun f => ⟨Q.ginzburgArrowSubstitutionComponent k τ i j f.val,hτ f.val f.property⟩
    left_inv := fun f => Subtype.ext (Q.ginzburgArrowSubstitutionComponent_inverse k τ σ hτσ i j f.val)
    right_inv := fun f => Subtype.ext (Q.ginzburgArrowSubstitutionComponent_inverse k σ τ hστ i j f.val)
    map_add' := fun f g => Subtype.ext (map_add _ f.val g.val)
    map_smul' := fun a f => Subtype.ext (map_smul _ a f.val) }

@[simp] theorem ginzburgArrowSubstitutionRestrictedEquiv_coe
    (σ τ : Q.GinzburgArrowReplacement k)
    (hστ : ∀ a, Q.ginzburgArrowSubstitutionComponent k σ (a.source Q) (a.target Q) (τ a) =
      Q.ginzburgIdentityArrowReplacement k a)
    (hτσ : ∀ a, Q.ginzburgArrowSubstitutionComponent k τ (a.source Q) (a.target Q) (σ a) =
      Q.ginzburgIdentityArrowReplacement k a)
    (i j : Q.Vertex) (S : Submodule k (Q.GinzburgPathComponent k i j))
    (hσ : ∀ f ∈ S, Q.ginzburgArrowSubstitutionComponent k σ i j f ∈ S)
    (hτ : ∀ f ∈ S, Q.ginzburgArrowSubstitutionComponent k τ i j f ∈ S) (f : S) :
    (Q.ginzburgArrowSubstitutionRestrictedEquiv k σ τ hστ hτσ i j S hσ hτ f).val =
      Q.ginzburgArrowSubstitutionComponent k σ i j f.val := rfl

section GradedEquivalences
variable (σ τ : Q.GinzburgArrowReplacement k)
  (hστ : ∀ a, Q.ginzburgArrowSubstitutionComponent k σ (a.source Q) (a.target Q) (τ a) =
    Q.ginzburgIdentityArrowReplacement k a)
  (hτσ : ∀ a, Q.ginzburgArrowSubstitutionComponent k τ (a.source Q) (a.target Q) (σ a) =
    Q.ginzburgIdentityArrowReplacement k a)
  (hσq : ∀ a, σ a ∈ Q.ginzburgCohomologicalComponent k (a.source Q) (a.target Q)
    (a.cohomologicalDegree Q))
  (hτq : ∀ a, τ a ∈ Q.ginzburgCohomologicalComponent k (a.source Q) (a.target Q)
    (a.cohomologicalDegree Q))

noncomputable def ginzburgArrowSubstitutionCohomologicalEquiv
    (i j : Q.Vertex) (q : ℤ) :
    Q.ginzburgCohomologicalComponent k i j q ≃ₗ[k] Q.ginzburgCohomologicalComponent k i j q :=
  Q.ginzburgArrowSubstitutionRestrictedEquiv k σ τ hστ hτσ i j
    (Q.ginzburgCohomologicalComponent k i j q)
    (Q.ginzburgArrowSubstitutionComponent_mem_cohomological k σ hσq i j q)
    (Q.ginzburgArrowSubstitutionComponent_mem_cohomological k τ hτq i j q)

@[simp] theorem ginzburgArrowSubstitutionCohomologicalEquiv_coe
    (i j : Q.Vertex) (q : ℤ) (f : Q.ginzburgCohomologicalComponent k i j q) :
    (Q.ginzburgArrowSubstitutionCohomologicalEquiv k σ τ hστ hτσ hσq hτq i j q f).val =
      Q.ginzburgArrowSubstitutionComponent k σ i j f.val := rfl

variable (hσc : ∀ a, σ a ∈ Q.ginzburgCutComponent k (a.source Q) (a.target Q) (a.cutDegree Q))
  (hτc : ∀ a, τ a ∈ Q.ginzburgCutComponent k (a.source Q) (a.target Q) (a.cutDegree Q))

noncomputable def ginzburgArrowSubstitutionCutCohomologicalEquiv
    (i j : Q.Vertex) (q c : ℤ) :
    Q.ginzburgCutCohomologicalComponent k i j q c ≃ₗ[k]
      Q.ginzburgCutCohomologicalComponent k i j q c :=
  Q.ginzburgArrowSubstitutionRestrictedEquiv k σ τ hστ hτσ i j
    (Q.ginzburgCutCohomologicalComponent k i j q c)
    (fun f hf => ⟨Q.ginzburgArrowSubstitutionComponent_mem_cohomological k σ hσq i j q f hf.1,
      Q.ginzburgArrowSubstitutionComponent_mem_cut k σ hσc i j c f hf.2⟩)
    (fun f hf => ⟨Q.ginzburgArrowSubstitutionComponent_mem_cohomological k τ hτq i j q f hf.1,
      Q.ginzburgArrowSubstitutionComponent_mem_cut k τ hτc i j c f hf.2⟩)

@[simp] theorem ginzburgArrowSubstitutionCutCohomologicalEquiv_coe
    (i j : Q.Vertex) (q c : ℤ) (f : Q.ginzburgCutCohomologicalComponent k i j q c) :
    (Q.ginzburgArrowSubstitutionCutCohomologicalEquiv k σ τ hστ hτσ hσq hτq hσc hτc i j q c f).val =
      Q.ginzburgArrowSubstitutionComponent k σ i j f.val := rfl

noncomputable def ginzburgArrowSubstitutionHomogeneousEquiv
    (hσ : ∀ a, σ a ∈ Q.ginzburgHomogeneousComponent k (a.source Q) (a.target Q)
      (a.cohomologicalDegree Q) (a.cutDegree Q) (a.winding Q))
    (hτ : ∀ a, τ a ∈ Q.ginzburgHomogeneousComponent k (a.source Q) (a.target Q)
      (a.cohomologicalDegree Q) (a.cutDegree Q) (a.winding Q))
    (i j : Q.Vertex) (q c w : ℤ) :
    Q.ginzburgHomogeneousComponent k i j q c w ≃ₗ[k] Q.ginzburgHomogeneousComponent k i j q c w :=
  Q.ginzburgArrowSubstitutionRestrictedEquiv k σ τ hστ hτσ i j
    (Q.ginzburgHomogeneousComponent k i j q c w)
    (Q.ginzburgArrowSubstitutionComponent_mem_homogeneous k σ hσ i j q c w)
    (Q.ginzburgArrowSubstitutionComponent_mem_homogeneous k τ hτ i j q c w)

@[simp] theorem ginzburgArrowSubstitutionHomogeneousEquiv_coe
    (hσ : ∀ a, σ a ∈ Q.ginzburgHomogeneousComponent k (a.source Q) (a.target Q)
      (a.cohomologicalDegree Q) (a.cutDegree Q) (a.winding Q))
    (hτ : ∀ a, τ a ∈ Q.ginzburgHomogeneousComponent k (a.source Q) (a.target Q)
      (a.cohomologicalDegree Q) (a.cutDegree Q) (a.winding Q))
    (i j : Q.Vertex) (q c w : ℤ) (f : Q.ginzburgHomogeneousComponent k i j q c w) :
    (Q.ginzburgArrowSubstitutionHomogeneousEquiv k σ τ hστ hτσ hσ hτ i j q c w f).val =
      Q.ginzburgArrowSubstitutionComponent k σ i j f.val := rfl

end GradedEquivalences
end ASGinzburg.CutQuiver
