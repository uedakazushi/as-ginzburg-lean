import ASGinzburg.ProjectiveResolutionHomExactness

/-! Actual Ext-three vanishing gives actual top Hom surjectivity for
an actual four-term projective resolution. -/
namespace CategoryTheory.ProjectiveResolution
open CategoryTheory.Limits
universe u v t
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{t} C]
variable {X : C} (P : ProjectiveResolution X)

 theorem hom_three_surjective_of_actual_ext_three_zero
    (h₄ : IsZero (P.complex.X 4)) (N : C)
    (hExt : ∀ e : Abelian.Ext.{t} X N 3, e = 0) (f : P.complex.X 3 ⟶ N) :
    ∃ g : P.complex.X 2 ⟶ N, P.complex.d 3 2 ≫ g = f := by
  have hK₀ : ∀ e : Abelian.Ext.{t} (kernel (P.π.f 0)) N 2, e = 0 := by
    intro e
    obtain ⟨z,hz⟩ := Abelian.Ext.contravariant_sequence_exact₁ P.shortExact₀ N e
      (show 1+2=3 from rfl) (hExt _)
    haveI : Projective (P.complex.X 0) := P.projective 0
    rw [Abelian.Ext.eq_zero_of_projective z, Abelian.Ext.comp_zero] at hz
    exact hz.symm
  have hK₁ : ∀ e : Abelian.Ext.{t} (kernel P.firstCover) N 1, e = 0 := by
    intro e
    obtain ⟨z,hz⟩ := Abelian.Ext.contravariant_sequence_exact₁ P.shortExact₁ N e
      (show 1+1=2 from rfl) (hK₀ _)
    haveI : Projective (P.complex.X 1) := P.projective 1
    rw [Abelian.Ext.eq_zero_of_projective z, Abelian.Ext.comp_zero] at hz
    exact hz.symm
  exact ASGinzburg.hom_extension_of_ext_one_zero (P.shortExact₂ h₄) N hK₁ f

end CategoryTheory.ProjectiveResolution
