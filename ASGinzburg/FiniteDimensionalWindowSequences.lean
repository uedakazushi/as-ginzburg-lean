import ASGinzburg.FiniteDimensionalWindows

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

theorem rightModuleWindow_simple (l r i : ℤ) (hl : l ≤ i) (hr : i ≤ r) :
    A.rightModuleWindowProperty l r (A.simpleRightModule i) := by
  intro j hj
  exact A.simpleRightModule_off_diagonal i j (by omega)

theorem rightModuleWindow_vertex_of_mono {M : A.RightModule} {l r i : ℤ}
    (hM : A.rightModuleWindowProperty l r M) (f : A.simpleRightModule i ⟶ M) [Mono f] :
    l ≤ i ∧ i ≤ r := by
  by_contra h
  have hi : i < l ∨ r < i := by omega
  have H := (hM i hi).of_mono ((A.rightModuleEvaluation i).map f)
  exact Simple.not_isZero ((A.rightModuleEvaluation i).obj (A.simpleRightModule i)) H

noncomputable def rightFiniteDimensionalShortComplex (S : ShortComplex A.RightModule)
    (h₁ : A.rightFiniteDimensionalProperty S.X₁) (h₂ : A.rightFiniteDimensionalProperty S.X₂)
    (h₃ : A.rightFiniteDimensionalProperty S.X₃) : ShortComplex A.RightFiniteDimensional where
  X₁ := ⟨S.X₁,h₁⟩
  X₂ := ⟨S.X₂,h₂⟩
  X₃ := ⟨S.X₃,h₃⟩
  f := ObjectProperty.homMk S.f
  g := ObjectProperty.homMk S.g
  zero := by
    apply ObjectProperty.hom_ext
    exact S.zero

theorem rightFiniteDimensionalShortComplex_shortExact {S : ShortComplex A.RightModule}
    (hS : S.ShortExact)
    (h₁ : A.rightFiniteDimensionalProperty S.X₁) (h₂ : A.rightFiniteDimensionalProperty S.X₂)
    (h₃ : A.rightFiniteDimensionalProperty S.X₃) :
    (A.rightFiniteDimensionalShortComplex S h₁ h₂ h₃).ShortExact := by
  let T := A.rightFiniteDimensionalShortComplex S h₁ h₂ h₃
  have hE : (T.map A.rightFiniteDimensionalProperty.ι).Exact := hS.exact
  have hM : Mono T.f := A.rightFiniteDimensionalProperty.ι.mono_of_mono_map (by
    change Mono S.f; exact hS.mono_f)
  have hG : Epi T.g := A.rightFiniteDimensionalProperty.ι.epi_of_epi_map (by
    change Epi S.g; exact hS.epi_g)
  exact {
    exact := (T.exact_map_iff_of_faithful A.rightFiniteDimensionalProperty.ι).mp hE
    mono_f := hM
    epi_g := hG }
end ASGinzburg.ZAlgebra
