import work.ASGinzburgDraft.GinzburgArrowSubstitution

/-! Literal inverse identities on extended generators imply inverse
maps on every actual Ginzburg path component. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgIdentityArrowReplacement : Q.GinzburgArrowReplacement k :=
  fun a => Finsupp.single (Q.ginzburgArrowPath a) 1

theorem ginzburgArrowSubstitutionPath_identity {i j : Q.Vertex} (p : Q.GinzburgPath i j) :
    Q.ginzburgArrowSubstitutionPath k (Q.ginzburgIdentityArrowReplacement k) p =
      Finsupp.single p 1 := by
  induction p with
  | nil => simp [ginzburgArrowSubstitutionPath,ginzburgPathId]
  | @snoc j p a h ih =>
    subst j
    simp [ginzburgArrowSubstitutionPath,ginzburgIdentityArrowReplacement,ginzburgArrowPath,
      ih,GinzburgPath.comp]

theorem ginzburgArrowSubstitutionComponent_identity (i j : Q.Vertex)
    (f : Q.GinzburgPathComponent k i j) :
    Q.ginzburgArrowSubstitutionComponent k (Q.ginzburgIdentityArrowReplacement k) i j f = f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g ih ih' => simp [map_add,ih,ih']
  | single p a => simp [Q.ginzburgArrowSubstitutionPath_identity,Finsupp.smul_single]

theorem ginzburgArrowSubstitutionComponent_inverse_on_path
    (σ τ : Q.GinzburgArrowReplacement k)
    (h : ∀ a, Q.ginzburgArrowSubstitutionComponent k σ (a.source Q) (a.target Q) (τ a) =
      Q.ginzburgIdentityArrowReplacement k a)
    {i j : Q.Vertex} (p : Q.GinzburgPath i j) :
    Q.ginzburgArrowSubstitutionComponent k σ i j (Q.ginzburgArrowSubstitutionPath k τ p) =
      Finsupp.single p 1 := by
  induction p with
  | nil =>
    simpa only [ginzburgArrowSubstitutionPath,ginzburgPathId] using
      Q.ginzburgArrowSubstitutionComponent_id k σ i
  | @snoc j p a ha ih =>
    subst j
    rw [ginzburgArrowSubstitutionPath,Q.ginzburgArrowSubstitutionComponent_comp,h a,ih]
    simp [ginzburgIdentityArrowReplacement,ginzburgArrowPath,GinzburgPath.comp]

theorem ginzburgArrowSubstitutionComponent_inverse
    (σ τ : Q.GinzburgArrowReplacement k)
    (h : ∀ a, Q.ginzburgArrowSubstitutionComponent k σ (a.source Q) (a.target Q) (τ a) =
      Q.ginzburgIdentityArrowReplacement k a)
    (i j : Q.Vertex) (f : Q.GinzburgPathComponent k i j) :
    Q.ginzburgArrowSubstitutionComponent k σ i j
      (Q.ginzburgArrowSubstitutionComponent k τ i j f) = f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g ih ih' => simp [map_add,ih,ih']
  | single p a =>
    simp [map_smul,Q.ginzburgArrowSubstitutionComponent_inverse_on_path k σ τ h,
      Finsupp.smul_single]

noncomputable def ginzburgArrowSubstitutionComponentEquiv
    (σ τ : Q.GinzburgArrowReplacement k)
    (hστ : ∀ a, Q.ginzburgArrowSubstitutionComponent k σ (a.source Q) (a.target Q) (τ a) =
      Q.ginzburgIdentityArrowReplacement k a)
    (hτσ : ∀ a, Q.ginzburgArrowSubstitutionComponent k τ (a.source Q) (a.target Q) (σ a) =
      Q.ginzburgIdentityArrowReplacement k a)
    (i j : Q.Vertex) : Q.GinzburgPathComponent k i j ≃ₗ[k] Q.GinzburgPathComponent k i j :=
  { Q.ginzburgArrowSubstitutionComponent k σ i j with
    invFun := Q.ginzburgArrowSubstitutionComponent k τ i j
    left_inv := Q.ginzburgArrowSubstitutionComponent_inverse k τ σ hτσ i j
    right_inv := Q.ginzburgArrowSubstitutionComponent_inverse k σ τ hστ i j }

@[simp] theorem ginzburgArrowSubstitutionComponentEquiv_apply
    (σ τ : Q.GinzburgArrowReplacement k)
    (hστ : ∀ a, Q.ginzburgArrowSubstitutionComponent k σ (a.source Q) (a.target Q) (τ a) =
      Q.ginzburgIdentityArrowReplacement k a)
    (hτσ : ∀ a, Q.ginzburgArrowSubstitutionComponent k τ (a.source Q) (a.target Q) (σ a) =
      Q.ginzburgIdentityArrowReplacement k a)
    (i j : Q.Vertex) (f : Q.GinzburgPathComponent k i j) :
    Q.ginzburgArrowSubstitutionComponentEquiv k σ τ hστ hτσ i j f =
      Q.ginzburgArrowSubstitutionComponent k σ i j f := rfl

@[simp] theorem ginzburgArrowSubstitutionComponentEquiv_symm_apply
    (σ τ : Q.GinzburgArrowReplacement k)
    (hστ : ∀ a, Q.ginzburgArrowSubstitutionComponent k σ (a.source Q) (a.target Q) (τ a) =
      Q.ginzburgIdentityArrowReplacement k a)
    (hτσ : ∀ a, Q.ginzburgArrowSubstitutionComponent k τ (a.source Q) (a.target Q) (σ a) =
      Q.ginzburgIdentityArrowReplacement k a)
    (i j : Q.Vertex) (f : Q.GinzburgPathComponent k i j) :
    (Q.ginzburgArrowSubstitutionComponentEquiv k σ τ hστ hτσ i j).symm f =
      Q.ginzburgArrowSubstitutionComponent k τ i j f := rfl

end ASGinzburg.CutQuiver
