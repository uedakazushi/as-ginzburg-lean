import work.ASGinzburgDraft.GinzburgArrowSubstitutionGrading
import work.ASGinzburgDraft.GinzburgArrowSubstitutionDifferential
import ASGinzburg.GinzburgRegularity

/-! Genuine cochain and homology isomorphisms from literal inverse
generator substitutions and proved generator differential compatibility. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]
variable (σ τ : Q.GinzburgArrowReplacement k) (φ ψ : Q.Potential k)
  (hστ : ∀ a, Q.ginzburgArrowSubstitutionComponent k σ (a.source Q) (a.target Q) (τ a) =
    Q.ginzburgIdentityArrowReplacement k a)
  (hτσ : ∀ a, Q.ginzburgArrowSubstitutionComponent k τ (a.source Q) (a.target Q) (σ a) =
    Q.ginzburgIdentityArrowReplacement k a)
  (hσDegree : ∀ a, σ a ∈ Q.ginzburgCohomologicalComponent k (a.source Q) (a.target Q)
    (a.cohomologicalDegree Q))
  (hτDegree : ∀ a, τ a ∈ Q.ginzburgCohomologicalComponent k (a.source Q) (a.target Q)
    (a.cohomologicalDegree Q))
  (hDifferential : ∀ a, Q.ginzburgDifferential k ψ (a.source Q) (a.target Q) (σ a) =
    Q.ginzburgArrowSubstitutionComponent k σ (a.source Q) (a.target Q)
      (Q.ginzburgGeneratorDifferential k φ a))

noncomputable def ginzburgArrowSubstitutionCochainIso (i j : Q.Vertex) :
    Q.ginzburgCochainComplex k φ i j ≅ Q.ginzburgCochainComplex k ψ i j :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => (Q.ginzburgArrowSubstitutionCohomologicalEquiv k σ τ
      hστ hτσ hσDegree hτDegree i j q).toModuleIso) (by
        intro q r hqr
        have hr : q + 1 = r := hqr
        subst r
        rw [Q.ginzburgCochainComplex_d,Q.ginzburgCochainComplex_d]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro f
        apply Subtype.ext
        exact Q.ginzburgArrowSubstitutionComponent_differential k σ φ ψ
          hσDegree hDifferential i j f.val)

noncomputable def ginzburgArrowSubstitutionHomologyIso (i j : Q.Vertex) (q : ℤ) :
    Q.ginzburgHomology k φ i j q ≅ Q.ginzburgHomology k ψ i j q :=
  (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℤ) q).mapIso
    (Q.ginzburgArrowSubstitutionCochainIso k σ τ φ ψ hστ hτσ hσDegree hτDegree
      hDifferential i j)

include hστ hτσ hσDegree hτDegree hDifferential in
theorem ginzburgRegular_iff_of_inverse_generator_substitution :
    Q.GinzburgRegular k φ ↔ Q.GinzburgRegular k ψ := by
  constructor
  · intro h
    apply (Q.ginzburgRegular_iff_components k ψ).mpr
    intro i j q hq
    have hz := (Q.ginzburgRegular_iff_components k φ).mp h i j q hq
    exact hz.of_iso (Q.ginzburgArrowSubstitutionHomologyIso k σ τ φ ψ
      hστ hτσ hσDegree hτDegree hDifferential i j q).symm
  · intro h
    apply (Q.ginzburgRegular_iff_components k φ).mpr
    intro i j q hq
    have hz := (Q.ginzburgRegular_iff_components k ψ).mp h i j q hq
    exact hz.of_iso (Q.ginzburgArrowSubstitutionHomologyIso k σ τ φ ψ
      hστ hτσ hσDegree hτDegree hDifferential i j q)

end ASGinzburg.CutQuiver
