import ASGinzburg.CutQuiver
import ASGinzburg.RightModuleSimpleHom

/-!
# Actual finite minimal sequences from the AS definition

The terms in (1.6) are finite coproducts indexed by arrows of the unrolled
quiver. ASResolution bundles the actual differentials, exactness, endpoint
monicity, and radical containment. Existence is not asserted for arbitrary A.
-/

namespace ASGinzburg.CutQuiver
variable (Q : CutQuiver)

/-- Incoming unrolled arrows are indexed by the original finite arrows, without choosing algebra elements. -/
abbrev incomingArrows (v : Q.LiftVertex) := { a : Q.Arrow // Q.target a = v.1 }
/-- Outgoing unrolled arrows are indexed by the original finite arrows. -/
abbrev outgoingArrows (v : Q.LiftVertex) := { a : Q.Arrow // Q.source a = v.1 }

instance incomingArrowsFintype (v : Q.LiftVertex) : Fintype (Q.incomingArrows v) := by
  dsimp [incomingArrows]
  infer_instance
instance outgoingArrowsFintype (v : Q.LiftVertex) : Fintype (Q.outgoingArrows v) := by
  dsimp [outgoingArrows]
  infer_instance

def incomingSource (v : Q.LiftVertex) (a : Q.incomingArrows v) : Q.LiftVertex :=
  Q.liftedSource a.val (v.2 - Q.cutDegree a.val)
def outgoingTarget (v : Q.LiftVertex) (a : Q.outgoingArrows v) : Q.LiftVertex :=
  Q.liftedTarget a.val v.2

@[simp] theorem incoming_liftedTarget (v : Q.LiftVertex) (a : Q.incomingArrows v) :
    Q.liftedTarget a.val (v.2 - Q.cutDegree a.val) = v := by
  apply Prod.ext
  · exact a.property
  · simp [liftedTarget]

@[simp] theorem outgoing_liftedSource (v : Q.LiftVertex) (a : Q.outgoingArrows v) :
    Q.liftedSource a.val v.2 = v := by
  apply Prod.ext
  · exact a.property
  · rfl

theorem incomingSource_height_lt (v : Q.LiftVertex) (a : Q.incomingArrows v) :
    Q.height (Q.incomingSource v a) < Q.height v := by
  simpa [incomingSource] using Q.lifted_arrow_increases_height a.val (v.2 - Q.cutDegree a.val)

theorem outgoingTarget_height_gt (v : Q.LiftVertex) (a : Q.outgoingArrows v) :
    Q.height v < Q.height (Q.outgoingTarget v a) := by
  simpa [outgoingTarget] using Q.lifted_arrow_increases_height a.val v.2

end ASGinzburg.CutQuiver

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

/-- Coproduct projectivity without restricting the indexing universe to the Hom universe. -/
theorem rightModule_coproduct_projective {β : Type*} (g : β → A.RightModule)
    [HasCoproduct g] [∀ b, Projective (g b)] : Projective (∐ g) where
  factors := by
    intro M N f e he
    refine ⟨Sigma.desc (fun b => Projective.factorThru (Sigma.ι g b ≫ f) e), ?_⟩
    apply Sigma.hom_ext
    intro b
    simp only [Sigma.ι_desc_assoc, Projective.factorThru_comp]

/-- Degree-one term of (1.6): one representable at each incoming arrow source. -/
noncomputable def asResolutionTerm₁ (v : Q.LiftVertex) : A.RightModule :=
  ∐ fun a : Q.incomingArrows v => A.representable (Q.height (Q.incomingSource v a))

/-- Degree-two term of (1.6): one representable at each outgoing target of τ⁻¹v. -/
noncomputable def asResolutionTerm₂ (v : Q.LiftVertex) : A.RightModule :=
  ∐ fun a : Q.outgoingArrows (Q.tau.symm v) =>
    A.representable (Q.height (Q.outgoingTarget (Q.tau.symm v) a))

noncomputable instance asResolutionTerm₁Projective (v : Q.LiftVertex) :
    Projective (A.asResolutionTerm₁ Q v) := by
  dsimp [asResolutionTerm₁]
  exact A.rightModule_coproduct_projective _
noncomputable instance asResolutionTerm₂Projective (v : Q.LiftVertex) :
    Projective (A.asResolutionTerm₂ Q v) := by
  dsimp [asResolutionTerm₂]
  exact A.rightModule_coproduct_projective _

/-- Actual data and proof obligations of the finite minimal sequence in (1.6).
Existence of this structure is part (i) of the paper's AS definition, not proved for arbitrary A. -/
structure ASResolution (v : Q.LiftVertex) where
  d₁ : A.asResolutionTerm₁ Q v ⟶ A.representable (Q.height v)
  d₂ : A.asResolutionTerm₂ Q v ⟶ A.asResolutionTerm₁ Q v
  d₃ : A.representable (Q.height (Q.tau.symm v)) ⟶ A.asResolutionTerm₂ Q v
  d₁_π : d₁ ≫ A.simpleRightModuleπ (Q.height v) = 0
  d₂_d₁ : d₂ ≫ d₁ = 0
  d₃_d₂ : d₃ ≫ d₂ = 0
  exact₀ : (ShortComplex.mk d₁ (A.simpleRightModuleπ (Q.height v)) d₁_π).Exact
  exact₁ : (ShortComplex.mk d₂ d₁ d₂_d₁).Exact
  exact₂ : (ShortComplex.mk d₃ d₂ d₃_d₂).Exact
  [mono_d₃ : Mono d₃]
  minimal₁ : A.IsMinimalMorphism d₁
  minimal₂ : A.IsMinimalMorphism d₂
  minimal₃ : A.IsMinimalMorphism d₃

namespace ASResolution
variable {A Q} {v : Q.LiftVertex} (R : A.ASResolution Q v)

theorem hom_d₁_simple_zero (i : ℤ) (f : A.representable (Q.height v) ⟶ A.simpleRightModule i) :
    R.d₁ ≫ f = 0 := A.minimalMorphism_comp_simple_eq_zero R.d₁ R.minimal₁ i f

theorem hom_d₂_simple_zero (i : ℤ) (f : A.asResolutionTerm₁ Q v ⟶ A.simpleRightModule i) :
    R.d₂ ≫ f = 0 := A.minimalMorphism_comp_simple_eq_zero R.d₂ R.minimal₂ i f

theorem hom_d₃_simple_zero (i : ℤ) (f : A.asResolutionTerm₂ Q v ⟶ A.simpleRightModule i) :
    R.d₃ ≫ f = 0 := A.minimalMorphism_comp_simple_eq_zero R.d₃ R.minimal₃ i f

end ASResolution
end ASGinzburg.ZAlgebra
