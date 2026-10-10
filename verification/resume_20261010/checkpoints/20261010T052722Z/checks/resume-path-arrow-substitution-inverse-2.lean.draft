import work.ASGinzburgDraft.PathArrowSubstitution
import ASGinzburg.FiniteComponentIdempotents

/-! Inverse substitutions need only be checked on actual arrows. Their
free extensions are then inverse genuine path-algebra automorphisms. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def pathIdentityArrowReplacement : Q.PathArrowReplacement k :=
  fun a => Finsupp.single (Path.snoc (.nil (Q.source a)) a rfl) 1

theorem pathArrowSubstitutionPath_identity {i j : Q.Vertex} (p : Q.Path i j) :
    Q.pathArrowSubstitutionPath k (Q.pathIdentityArrowReplacement k) p = Finsupp.single p 1 := by
  induction p with
  | nil => simp [pathArrowSubstitutionPath,pathId]
  | @snoc j p a h ih =>
    subst j
    simp [pathArrowSubstitutionPath,pathIdentityArrowReplacement,ih,Path.comp]

theorem pathArrowSubstitutionComponent_identity (i j : Q.Vertex)
    (f : Q.PathComponent k i j) :
    Q.pathArrowSubstitutionComponent k (Q.pathIdentityArrowReplacement k) i j f = f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g ih ih' => simp [map_add,ih,ih']
  | single p a => simp [Q.pathArrowSubstitutionPath_identity,Finsupp.smul_single]

theorem pathArrowSubstitutionComponent_inverse_on_path
    (σ τ : Q.PathArrowReplacement k)
    (h : ∀ a, Q.pathArrowSubstitutionComponent k σ (Q.source a) (Q.target a) (τ a) =
      Q.pathIdentityArrowReplacement k a)
    {i j : Q.Vertex} (p : Q.Path i j) :
    Q.pathArrowSubstitutionComponent k σ i j (Q.pathArrowSubstitutionPath k τ p) =
      Finsupp.single p 1 := by
  induction p with
  | nil =>
    simpa only [pathArrowSubstitutionPath,pathId] using
      Q.pathArrowSubstitutionComponent_id k σ i
  | @snoc j p a ha ih =>
    subst j
    rw [pathArrowSubstitutionPath,Q.pathArrowSubstitutionComponent_comp,h a,ih]
    simp [pathIdentityArrowReplacement,Path.comp]

theorem pathArrowSubstitutionComponent_inverse
    (σ τ : Q.PathArrowReplacement k)
    (h : ∀ a, Q.pathArrowSubstitutionComponent k σ (Q.source a) (Q.target a) (τ a) =
      Q.pathIdentityArrowReplacement k a)
    (i j : Q.Vertex) (f : Q.PathComponent k i j) :
    Q.pathArrowSubstitutionComponent k σ i j
      (Q.pathArrowSubstitutionComponent k τ i j f) = f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g ih ih' => simp [map_add,ih,ih']
  | single p a =>
    simp [map_smul,Q.pathArrowSubstitutionComponent_inverse_on_path k σ τ h,
      Finsupp.smul_single]

theorem pathArrowSubstitution_inverse
    (σ τ : Q.PathArrowReplacement k)
    (h : ∀ a, Q.pathArrowSubstitutionComponent k σ (Q.source a) (Q.target a) (τ a) =
      Q.pathIdentityArrowReplacement k a)
    (x : Q.PathRing k) :
    Q.pathArrowSubstitution k σ (Q.pathArrowSubstitution k τ x) = x := by
  funext i j
  exact Q.pathArrowSubstitutionComponent_inverse k σ τ h i j (x i j)

noncomputable def pathArrowSubstitutionAlgEquiv
    (σ τ : Q.PathArrowReplacement k)
    (hστ : ∀ a, Q.pathArrowSubstitutionComponent k σ (Q.source a) (Q.target a) (τ a) =
      Q.pathIdentityArrowReplacement k a)
    (hτσ : ∀ a, Q.pathArrowSubstitutionComponent k τ (Q.source a) (Q.target a) (σ a) =
      Q.pathIdentityArrowReplacement k a) : Q.PathRing k ≃ₐ[k] Q.PathRing k :=
  AlgEquiv.ofAlgHom (Q.pathArrowSubstitution k σ) (Q.pathArrowSubstitution k τ)
    (by apply AlgHom.ext; intro x; exact Q.pathArrowSubstitution_inverse k σ τ hστ x)
    (by apply AlgHom.ext; intro x; exact Q.pathArrowSubstitution_inverse k τ σ hτσ x)

theorem pathArrowSubstitution_fixes_vertex (σ : Q.PathArrowReplacement k) (i : Q.Vertex) :
    Q.pathArrowSubstitution k σ ((Q.pathComponentAlgebra k).totalIdempotent i) =
      (Q.pathComponentAlgebra k).totalIdempotent i := by
  change Q.pathArrowSubstitution k σ
    ((Q.pathComponentAlgebra k).totalComponent i i (Q.pathId k i)) = _
  rw [Q.pathArrowSubstitution_component,Q.pathArrowSubstitutionComponent_id]
  rfl

end ASGinzburg.CutQuiver
