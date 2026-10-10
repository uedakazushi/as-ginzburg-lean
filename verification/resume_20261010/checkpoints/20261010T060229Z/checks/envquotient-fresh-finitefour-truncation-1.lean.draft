import work.ASGinzburgDraft.FiniteFourTermProjectiveResolution
import work.ASGinzburgDraft.FourTermTruncationOfResolution

/-! Truncating an actual projective resolution with zero fourth object
retains finite generation of its first four original module objects. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
universe u v
variable {R : Type u} [Ring R] {X : ModuleCat.{v} R}

noncomputable def finiteFourTermTruncationOfResolution
    (P : ProjectiveResolution X) (h₄ : IsZero (P.complex.X 4))
    (h₀ : Module.Finite R (P.complex.X 0))
    (h₁ : Module.Finite R (P.complex.X 1))
    (h₂ : Module.Finite R (P.complex.X 2))
    (h₃ : Module.Finite R (P.complex.X 3)) :
    FiniteFourTermProjectiveResolution X where
  toFourTermProjectiveResolution := fourTermTruncationOfResolution P h₄
  finite₀ := h₀
  finite₁ := h₁
  finite₂ := h₂
  finite₃ := h₃

theorem nonempty_finiteFourTermProjectiveResolution_of_resolution
    (P : ProjectiveResolution X) (h₄ : IsZero (P.complex.X 4))
    (h₀ : Module.Finite R (P.complex.X 0))
    (h₁ : Module.Finite R (P.complex.X 1))
    (h₂ : Module.Finite R (P.complex.X 2))
    (h₃ : Module.Finite R (P.complex.X 3)) :
    Nonempty (FiniteFourTermProjectiveResolution X) :=
  ⟨finiteFourTermTruncationOfResolution P h₄ h₀ h₁ h₂ h₃⟩

theorem exists_fourTermProjectiveResolution_finite_of_resolution
    (P : ProjectiveResolution X) (h₄ : IsZero (P.complex.X 4))
    (h₀ : Module.Finite R (P.complex.X 0))
    (h₁ : Module.Finite R (P.complex.X 1))
    (h₂ : Module.Finite R (P.complex.X 2))
    (h₃ : Module.Finite R (P.complex.X 3)) :
    ∃ F : FourTermProjectiveResolution X, ∀ n, Module.Finite R (F.term n) := by
  let F := finiteFourTermTruncationOfResolution P h₄ h₀ h₁ h₂ h₃
  exact ⟨F.toFourTermProjectiveResolution, F.term_finite⟩

end ASGinzburg
