import ASGinzburg.FoundationProjectives
import ASGinzburg.FourTermProjectiveResolution

/-! The original AS sequence gives an actual finite projective resolution
of each foundation vertex simple. Its degree-three term is genuinely zero;
minimal relation representatives still have to be extracted from degree two. -/
namespace ASGinzburg.ZAlgebra.ASResolution
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k} {Q : CutQuiver}
  {j : Q.Vertex} (R : A.ASResolution Q (j,0))

noncomputable def foundationFourTermProjectiveResolution :
    FourTermProjectiveResolution
      ((A.foundationRestriction Q).obj (A.simpleRightModule (Q.height (j,0)))) where
  P₀ := (A.foundationRestriction Q).obj (A.representable (Q.height (j,0)))
  P₁ := (A.foundationRestriction Q).obj (A.asResolutionTerm₁ Q (j,0))
  P₂ := (A.foundationRestriction Q).obj (A.asResolutionTerm₂ Q (j,0))
  P₃ := (A.foundationRestriction Q).obj (A.representable (Q.height (Q.tau.symm (j,0))))
  projective₀ := by
    simpa [CutQuiver.height,foundationRepresentable] using
      (inferInstance : Projective (A.foundationRepresentable Q j))
  projective₁ := A.foundation_restricted_first_projective Q j
  projective₂ := A.foundation_restricted_second_projective Q j
  projective₃ := (A.foundation_as_left_term_isZero Q j).projective
  π := (A.foundationRestriction Q).map (A.simpleRightModuleπ (Q.height (j,0)))
  d₁ := (A.foundationRestriction Q).map R.d₁
  d₂ := (A.foundationRestriction Q).map R.d₂
  d₃ := (A.foundationRestriction Q).map R.d₃
  epi_π := by infer_instance
  mono_d₃ := by
    letI := R.mono_d₃
    infer_instance
  d₁_π := by rw [←Functor.map_comp,R.d₁_π,Functor.map_zero]
  d₂_d₁ := by rw [←Functor.map_comp,R.d₂_d₁,Functor.map_zero]
  d₃_d₂ := by rw [←Functor.map_comp,R.d₃_d₂,Functor.map_zero]
  exact₀ := R.exact₀.map (A.foundationRestriction Q)
  exact₁ := R.exact₁.map (A.foundationRestriction Q)
  exact₂ := R.exact₂.map (A.foundationRestriction Q)

noncomputable def foundationProjectiveResolution :
    ProjectiveResolution
      ((A.foundationRestriction Q).obj (A.simpleRightModule (Q.height (j,0)))) :=
  R.foundationFourTermProjectiveResolution.toProjectiveResolution

theorem foundationProjectiveResolution_X_three_isZero :
    IsZero (R.foundationProjectiveResolution.complex.X 3) :=
  A.foundation_as_left_term_isZero Q j

theorem foundationProjectiveResolution_X_ge_four_isZero (n : ℕ) :
    IsZero (R.foundationProjectiveResolution.complex.X (n+4)) :=
  R.foundationFourTermProjectiveResolution.complex_isZero_ge_four n

end ASGinzburg.ZAlgebra.ASResolution
