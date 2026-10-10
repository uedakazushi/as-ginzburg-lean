import work.ASGinzburgDraft.TriangleQuadraticTerms
import work.ASGinzburgDraft.RightModuleIsoConjugation

/-! The literal minimal quadratic resolution (5.1), with no periodicity
condition, and its comparison with the concrete triangle AS sequence. -/

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

/-- The actual minimal sequence
`0 → P_(i−3) → P_(i−2)^3 → P_(i−1)^3 → P_i → s_i → 0`. -/
structure QuadraticASResolution (i : ℤ) where
  d₁ : A.quadraticTriple (i - 1) ⟶ A.representable i
  d₂ : A.quadraticTriple (i - 2) ⟶ A.quadraticTriple (i - 1)
  d₃ : A.representable (i - 3) ⟶ A.quadraticTriple (i - 2)
  d₁_π : d₁ ≫ A.simpleRightModuleπ i = 0
  d₂_d₁ : d₂ ≫ d₁ = 0
  d₃_d₂ : d₃ ≫ d₂ = 0
  exact₀ : (ShortComplex.mk d₁ (A.simpleRightModuleπ i) d₁_π).Exact
  exact₁ : (ShortComplex.mk d₂ d₁ d₂_d₁).Exact
  exact₂ : (ShortComplex.mk d₃ d₂ d₃_d₂).Exact
  [mono_d₃ : Mono d₃]
  minimal₁ : A.IsMinimalMorphism d₁
  minimal₂ : A.IsMinimalMorphism d₂
  minimal₃ : A.IsMinimalMorphism d₃

noncomputable def ASResolution.toQuadraticASResolution {A : ZAlgebra.{u,v} k}
    {w : triangle333.LiftVertex} (R : A.ASResolution triangle333 w) :
    A.QuadraticASResolution (triangle333.height w) := by
  let e₀ := Iso.refl (A.representable (triangle333.height w))
  let es := Iso.refl (A.simpleRightModule (triangle333.height w))
  let e₁ := A.triangleASFirstTermIso w
  let e₂ := A.triangleASSecondTermIso w
  let e₃ := A.triangleASTopTermIso w
  let d₁ := A.conjugateRightModuleMap e₁ e₀ R.d₁
  let d₂ := A.conjugateRightModuleMap e₂ e₁ R.d₂
  let d₃ := A.conjugateRightModuleMap e₃ e₂ R.d₃
  have hπ : A.conjugateRightModuleMap e₀ es (A.simpleRightModuleπ (triangle333.height w)) =
      A.simpleRightModuleπ (triangle333.height w) := by
    simp [conjugateRightModuleMap, e₀, es]
  have h₀ : d₁ ≫ A.simpleRightModuleπ (triangle333.height w) = 0 := by
    rw [← hπ]
    exact A.conjugateRightModuleMap_comp_zero e₁ e₀ es _ _ R.d₁_π
  have h₁ : d₂ ≫ d₁ = 0 := A.conjugateRightModuleMap_comp_zero e₂ e₁ e₀ _ _ R.d₂_d₁
  have h₂ : d₃ ≫ d₂ = 0 := A.conjugateRightModuleMap_comp_zero e₃ e₂ e₁ _ _ R.d₃_d₂
  refine {
    d₁ := d₁
    d₂ := d₂
    d₃ := d₃
    d₁_π := h₀
    d₂_d₁ := h₁
    d₃_d₂ := h₂
    exact₀ := ?_
    exact₁ := A.conjugateRightModuleShortComplex_exact
      (ShortComplex.mk R.d₂ R.d₁ R.d₂_d₁) R.exact₁ e₂ e₁ e₀
    exact₂ := A.conjugateRightModuleShortComplex_exact
      (ShortComplex.mk R.d₃ R.d₂ R.d₃_d₂) R.exact₂ e₃ e₂ e₁
    mono_d₃ := ?_
    minimal₁ := A.conjugateRightModuleMap_minimal e₁ e₀ R.d₁ R.minimal₁
    minimal₂ := A.conjugateRightModuleMap_minimal e₂ e₁ R.d₂ R.minimal₂
    minimal₃ := A.conjugateRightModuleMap_minimal e₃ e₂ R.d₃ R.minimal₃ }
  · have he := A.conjugateRightModuleShortComplex_exact
      (ShortComplex.mk R.d₁ (A.simpleRightModuleπ (triangle333.height w)) R.d₁_π)
      R.exact₀ e₁ e₀ es
    simpa only [hπ] using he
  · haveI := R.mono_d₃
    dsimp only [d₃, conjugateRightModuleMap]
    infer_instance

noncomputable def QuadraticASResolution.toTriangleASResolution {A : ZAlgebra.{u,v} k}
    (w : triangle333.LiftVertex) (R : A.QuadraticASResolution (triangle333.height w)) :
    A.ASResolution triangle333 w := by
  let e₀ := Iso.refl (A.representable (triangle333.height w))
  let es := Iso.refl (A.simpleRightModule (triangle333.height w))
  let e₁ := (A.triangleASFirstTermIso w).symm
  let e₂ := (A.triangleASSecondTermIso w).symm
  let e₃ := (A.triangleASTopTermIso w).symm
  let d₁ := A.conjugateRightModuleMap e₁ e₀ R.d₁
  let d₂ := A.conjugateRightModuleMap e₂ e₁ R.d₂
  let d₃ := A.conjugateRightModuleMap e₃ e₂ R.d₃
  have hπ : A.conjugateRightModuleMap e₀ es (A.simpleRightModuleπ (triangle333.height w)) =
      A.simpleRightModuleπ (triangle333.height w) := by
    simp [conjugateRightModuleMap, e₀, es]
  have h₀ : d₁ ≫ A.simpleRightModuleπ (triangle333.height w) = 0 := by
    rw [← hπ]
    exact A.conjugateRightModuleMap_comp_zero e₁ e₀ es _ _ R.d₁_π
  have h₁ : d₂ ≫ d₁ = 0 := A.conjugateRightModuleMap_comp_zero e₂ e₁ e₀ _ _ R.d₂_d₁
  have h₂ : d₃ ≫ d₂ = 0 := A.conjugateRightModuleMap_comp_zero e₃ e₂ e₁ _ _ R.d₃_d₂
  refine {
    d₁ := d₁
    d₂ := d₂
    d₃ := d₃
    d₁_π := h₀
    d₂_d₁ := h₁
    d₃_d₂ := h₂
    exact₀ := ?_
    exact₁ := A.conjugateRightModuleShortComplex_exact
      (ShortComplex.mk R.d₂ R.d₁ R.d₂_d₁) R.exact₁ e₂ e₁ e₀
    exact₂ := A.conjugateRightModuleShortComplex_exact
      (ShortComplex.mk R.d₃ R.d₂ R.d₃_d₂) R.exact₂ e₃ e₂ e₁
    mono_d₃ := ?_
    minimal₁ := A.conjugateRightModuleMap_minimal e₁ e₀ R.d₁ R.minimal₁
    minimal₂ := A.conjugateRightModuleMap_minimal e₂ e₁ R.d₂ R.minimal₂
    minimal₃ := A.conjugateRightModuleMap_minimal e₃ e₂ R.d₃ R.minimal₃ }
  · have he := A.conjugateRightModuleShortComplex_exact
      (ShortComplex.mk R.d₁ (A.simpleRightModuleπ (triangle333.height w)) R.d₁_π)
      R.exact₀ e₁ e₀ es
    simpa only [hπ] using he
  · haveI := R.mono_d₃
    dsimp only [d₃, conjugateRightModuleMap]
    infer_instance

theorem quadraticASResolution_nonempty_iff (w : triangle333.LiftVertex) :
    Nonempty (A.QuadraticASResolution (triangle333.height w)) ↔
      Nonempty (A.ASResolution triangle333 w) := by
  constructor
  · rintro ⟨R⟩
    exact ⟨R.toTriangleASResolution w⟩
  · rintro ⟨R⟩
    exact ⟨R.toQuadraticASResolution⟩

end ASGinzburg.ZAlgebra
