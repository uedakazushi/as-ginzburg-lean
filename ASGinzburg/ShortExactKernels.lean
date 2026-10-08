import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma

namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

noncomputable def shortExactSnakeInput {S T : ShortComplex C}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) : ShortComplex.SnakeInput C where
  L₀ := kernel φ
  L₁ := S
  L₂ := T
  L₃ := cokernel φ
  v₀₁ := kernel.ι φ
  v₁₂ := φ
  v₂₃ := cokernel.π φ
  w₀₂ := kernel.condition φ
  w₁₃ := cokernel.condition φ
  h₀ := kernelIsKernel φ
  h₃ := cokernelIsCokernel φ
  L₁_exact := hS.exact
  epi_L₁_g := hS.epi_g
  L₂_exact := hT.exact
  mono_L₂_f := hT.mono_f

theorem kernel_shortExact_of_epi_first {S T : ShortComplex C}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) [Epi φ.τ₁] :
    (kernel φ).ShortExact := by
  let K := shortExactSnakeInput hS hT φ
  change K.L₀.ShortExact
  have hz : IsZero K.L₃.X₁ := by
    letI : Epi K.v₁₂.τ₁ := inferInstanceAs (Epi φ.τ₁)
    exact CokernelCofork.IsColimit.isZero_of_epi K.h₃τ₁
  have hf : Mono K.L₀.f := by
    letI : Mono K.L₁.f := hS.mono_f
    haveI : Mono (K.v₀₁.τ₁ ≫ K.L₁.f) := inferInstance
    haveI : Mono (K.L₀.f ≫ K.v₀₁.τ₂) := by
      rw [← K.v₀₁.comm₁₂]
      infer_instance
    exact mono_of_mono K.L₀.f K.v₀₁.τ₂
  have hg : Epi K.L₀.g :=
    (ShortComplex.exact_iff_epi K.L₁' (hz.eq_of_tgt _ _)).mp K.L₁'_exact
  exact { exact := K.L₀_exact, mono_f := hf, epi_g := hg }
end ASGinzburg
