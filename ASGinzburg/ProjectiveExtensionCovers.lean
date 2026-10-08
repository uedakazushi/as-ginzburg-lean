import ASGinzburg.ShortExactKernels
import Mathlib.CategoryTheory.Preadditive.Projective.Basic

namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] {S : ShortComplex C}
  (hS : S.ShortExact) {P₁ P₃ : C} (p₁ : P₁ ⟶ S.X₁) (p₃ : P₃ ⟶ S.X₃) [Projective P₃]

noncomputable def extensionProjectiveπ : P₁ ⊞ P₃ ⟶ S.X₂ := by
  letI := hS.epi_g
  exact biprod.desc (p₁ ≫ S.f) (Projective.factorThru p₃ S.g)

@[simp] theorem extensionProjectiveπ_inl :
    biprod.inl ≫ extensionProjectiveπ hS p₁ p₃ = p₁ ≫ S.f := by
  simp [extensionProjectiveπ]

theorem extensionProjectiveπ_g :
    extensionProjectiveπ hS p₁ p₃ ≫ S.g = biprod.snd ≫ p₃ := by
  letI := hS.epi_g
  apply biprod.hom_ext'
  · simp [extensionProjectiveπ,Category.assoc,S.zero]
  · simp [extensionProjectiveπ]

noncomputable def extensionProjectiveCoverHom :
    (ShortComplex.mk (biprod.inl : P₁ ⟶ P₁ ⊞ P₃) biprod.snd (by simp)) ⟶ S where
  τ₁ := p₁
  τ₂ := extensionProjectiveπ hS p₁ p₃
  τ₃ := p₃
  comm₁₂ := (extensionProjectiveπ_inl hS p₁ p₃).symm
  comm₂₃ := extensionProjectiveπ_g hS p₁ p₃

noncomputable instance extensionProjectiveπEpi [Epi p₁] [Epi p₃] :
    Epi (extensionProjectiveπ hS p₁ p₃) := by
  letI := hS.epi_g
  let φ := extensionProjectiveCoverHom hS p₁ p₃
  letI : Epi φ.τ₁ := inferInstanceAs (Epi p₁)
  letI : Epi φ.τ₃ := inferInstanceAs (Epi p₃)
  exact ShortComplex.epi_τ₂_of_exact_of_epi φ hS.exact

theorem extensionProjectiveKernel_shortExact [Epi p₁] :
    (kernel (extensionProjectiveCoverHom hS p₁ p₃)).ShortExact := by
  letI : Epi (extensionProjectiveCoverHom hS p₁ p₃).τ₁ := inferInstanceAs (Epi p₁)
  exact kernel_shortExact_of_epi_first
    (ShortComplex.Splitting.ofHasBinaryBiproduct P₁ P₃).shortExact hS _

noncomputable def extensionProjectiveKernelLeftIso :
    (kernel (extensionProjectiveCoverHom hS p₁ p₃)).X₁ ≅ kernel p₁ :=
  PreservesKernel.iso (ShortComplex.π₁ : ShortComplex C ⥤ C) (extensionProjectiveCoverHom hS p₁ p₃)

noncomputable def extensionProjectiveKernelMiddleIso :
    (kernel (extensionProjectiveCoverHom hS p₁ p₃)).X₂ ≅
      kernel (extensionProjectiveπ hS p₁ p₃) :=
  PreservesKernel.iso (ShortComplex.π₂ : ShortComplex C ⥤ C) (extensionProjectiveCoverHom hS p₁ p₃)

noncomputable def extensionProjectiveKernelRightIso :
    (kernel (extensionProjectiveCoverHom hS p₁ p₃)).X₃ ≅ kernel p₃ :=
  PreservesKernel.iso (ShortComplex.π₃ : ShortComplex C ⥤ C) (extensionProjectiveCoverHom hS p₁ p₃)
end ASGinzburg
