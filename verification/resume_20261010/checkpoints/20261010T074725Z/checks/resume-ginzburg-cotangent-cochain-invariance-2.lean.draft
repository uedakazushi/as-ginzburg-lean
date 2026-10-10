import work.ASGinzburgDraft.GinzburgCotangentSubstitutionInverse
import work.ASGinzburgDraft.GinzburgCotangentLoopTransport
import work.ASGinzburgDraft.GinzburgArrowSubstitutionCochainIso

/-! The genuine nonlinear cotangent lift is an actual Ginzburg cochain
isomorphism. It preserves original regularity without added compatibility
or inverse assumptions. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgCotangentArrowReplacement_differential
    (E : Q.VertexCutPathAutomorphism k) (φ : Q.Potential k) (a : Q.GinzburgArrow) :
    Q.ginzburgDifferential k (VertexCutPathAutomorphism.potentialLinearEquiv Q k E φ)
      (a.source Q) (a.target Q) (Q.ginzburgCotangentArrowReplacement k E a) =
      Q.ginzburgArrowSubstitutionComponent k (Q.ginzburgCotangentArrowReplacement k E)
        (a.source Q) (a.target Q) (Q.ginzburgGeneratorDifferential k φ a) := by
  cases a with
  | original a =>
    change Q.ginzburgDifferential k _ _ _ (Q.originalGinzburgLinearMap k _ _ _) = _
    rw [Q.ginzburgDifferential_original]
    simp only [ginzburgGeneratorDifferential,map_zero]
  | dual a =>
    change Q.ginzburgDifferential k _ _ _ (Q.ginzburgCotangentDualImage k E a) =
      Q.ginzburgArrowSubstitutionComponent k _ _ _
        (Q.originalGinzburgLinearMap k _ _ (Q.pathCyclicDerivative k a φ))
    rw [Q.ginzburgCotangentDualImage_differential,Q.ginzburgCotangentSubstitution_original]
  | loop v =>
    exact (Q.ginzburgDifferential_generator k
      (VertexCutPathAutomorphism.potentialLinearEquiv Q k E φ) (.loop v)).trans
        (Q.ginzburgCotangentLoopDifferential_transport k E v).symm

noncomputable def ginzburgCotangentCochainIso
    (E : Q.VertexCutPathAutomorphism k) (φ : Q.Potential k) (i j : Q.Vertex) :
    Q.ginzburgCochainComplex k φ i j ≅
      Q.ginzburgCochainComplex k (VertexCutPathAutomorphism.potentialLinearEquiv Q k E φ) i j :=
  Q.ginzburgArrowSubstitutionCochainIso k
    (Q.ginzburgCotangentArrowReplacement k E) (Q.ginzburgCotangentArrowReplacement k (E⁻¹))
    φ (VertexCutPathAutomorphism.potentialLinearEquiv Q k E φ)
    (Q.ginzburgCotangentArrowReplacement_inverse k E)
    (Q.ginzburgCotangentArrowReplacement_inverse_reverse k E)
    (Q.ginzburgCotangentArrowReplacement_mem_cohomological k E)
    (Q.ginzburgCotangentArrowReplacement_mem_cohomological k (E⁻¹))
    (Q.ginzburgCotangentArrowReplacement_differential k E φ) i j

noncomputable def ginzburgCotangentHomologyIso
    (E : Q.VertexCutPathAutomorphism k) (φ : Q.Potential k) (i j : Q.Vertex) (q : ℤ) :
    Q.ginzburgHomology k φ i j q ≅
      Q.ginzburgHomology k (VertexCutPathAutomorphism.potentialLinearEquiv Q k E φ) i j q :=
  (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℤ) q).mapIso
    (Q.ginzburgCotangentCochainIso k E φ i j)

theorem ginzburgRegular_pathAutomorphism_iff
    (E : Q.VertexCutPathAutomorphism k) (φ : Q.Potential k) :
    Q.GinzburgRegular k (E • φ) ↔ Q.GinzburgRegular k φ := by
  change Q.GinzburgRegular k (VertexCutPathAutomorphism.potentialLinearEquiv Q k E φ) ↔ _
  exact (Q.ginzburgRegular_iff_of_inverse_generator_substitution k
    (Q.ginzburgCotangentArrowReplacement k E) (Q.ginzburgCotangentArrowReplacement k (E⁻¹))
    φ (VertexCutPathAutomorphism.potentialLinearEquiv Q k E φ)
    (Q.ginzburgCotangentArrowReplacement_inverse k E)
    (Q.ginzburgCotangentArrowReplacement_inverse_reverse k E)
    (Q.ginzburgCotangentArrowReplacement_mem_cohomological k E)
    (Q.ginzburgCotangentArrowReplacement_mem_cohomological k (E⁻¹))
    (Q.ginzburgCotangentArrowReplacement_differential k E φ)).symm

end ASGinzburg.CutQuiver
