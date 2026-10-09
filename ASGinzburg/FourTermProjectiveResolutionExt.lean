import ASGinzburg.ProjectiveResolutionSyzygies
import ASGinzburg.RightModuleExtSequence
import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-! Real Ext vanishing from a genuine four-term projective resolution.
No minimality, AS condition, or prescribed Ext duality is assumed. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

noncomputable def rightFourTermProjectiveResolutionExtShift
    {M : A.RightModule} (P : ProjectiveResolution M) (h₄ : IsZero (P.complex.X 4))
    (N : A.RightModule) (n : ℕ) :
    Abelian.Ext.{v} (P.complex.X 3) N (n+1) ≃ₗ[k] Abelian.Ext.{v} M N (n+4) :=
  ((A.rightModuleExtDimensionShift (P.shortExact₂ h₄) N n).trans
    (A.rightModuleExtDimensionShift P.shortExact₁ N (n+1))).trans
      (A.rightModuleExtDimensionShift P.shortExact₀ N (n+2))

theorem rightFourTermProjectiveResolution_ext_ge_four_eq_zero
    {M : A.RightModule} (P : ProjectiveResolution M) (h₄ : IsZero (P.complex.X 4))
    (N : A.RightModule) (n : ℕ) (e : Abelian.Ext.{v} M N (n+4)) : e=0 := by
  obtain ⟨x,rfl⟩ := (A.rightFourTermProjectiveResolutionExtShift P h₄ N n).surjective e
  rw [Abelian.Ext.eq_zero_of_projective x,LinearEquiv.map_zero]

theorem rightFourTermProjectiveResolution_hasProjectiveDimensionLE
    {M : A.RightModule} (P : ProjectiveResolution M) (h₄ : IsZero (P.complex.X 4)) :
    HasProjectiveDimensionLE M 3 := by
  apply HasProjectiveDimensionLT.mk
  intro n hn N e
  obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 4 m] at hm
  subst n
  exact A.rightFourTermProjectiveResolution_ext_ge_four_eq_zero P h₄ N m e

end ASGinzburg.ZAlgebra
