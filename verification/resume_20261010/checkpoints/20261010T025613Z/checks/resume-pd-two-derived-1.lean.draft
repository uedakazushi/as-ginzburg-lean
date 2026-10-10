import work.ASGinzburgDraft.ProjectiveDimensionThreeDerivedVanishing

/-! A projective-dimension bound by two gives a genuine resolution with
zero third term and vanishing third and higher additive left derivatives.
Nonzero third Tor can therefore certify a lower bound by three. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] {X : C}

noncomputable def projectiveDimensionTwoResolution (P : ProjectiveResolution X)
    (hX : HasProjectiveDimensionLE X 2) : ProjectiveResolution X := by
  have h₁ : HasProjectiveDimensionLT (kernel (P.π.f 0)) 2 :=
    P.shortExact₀.hasProjectiveDimensionLT_X₁ 2 inferInstance hX
  have h₂ : HasProjectiveDimensionLT (kernel P.firstCover) 1 :=
    P.shortExact₁.hasProjectiveDimensionLT_X₁ 1 inferInstance h₁
  letI : Projective (kernel P.firstCover) :=
    (projective_iff_hasProjectiveDimensionLT_one _).mpr h₂
  letI : Projective (kernel (𝟙 (kernel P.firstCover))) :=
    (isZero_kernel_of_mono (𝟙 (kernel P.firstCover))).projective
  exact (FourTermProjectiveResolution.ofKernelCovers
    (P.π.f 0) P.firstCover (𝟙 (kernel P.firstCover))).toProjectiveResolution

theorem projectiveDimensionTwoResolution_isZero_ge_three
    (P : ProjectiveResolution X) (hX : HasProjectiveDimensionLE X 2) (n : ℕ) :
    IsZero ((projectiveDimensionTwoResolution P hX).complex.X (n+3)) := by
  cases n with
  | zero =>
    change IsZero (kernel (𝟙 (kernel P.firstCover)))
    exact isZero_kernel_of_mono _
  | succ n =>
    change IsZero (0 : C)
    exact isZero_zero C

variable [HasProjectiveResolutions C] {D : Type*} [Category D] [Abelian D]

theorem leftDerived_isZero_of_projectiveDimensionLE_two
    (F : C ⥤ D) [F.Additive] (hX : HasProjectiveDimensionLE X 2) (n : ℕ) :
    IsZero ((F.leftDerived (n+3)).obj X) := by
  let P := projectiveDimensionTwoResolution (projectiveResolution X) hX
  let K := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  have hK : IsZero (K.homology (n+3)) :=
    (K.sc (n+3)).isZero_homology_of_isZero_X₂
      (F.map_isZero (projectiveDimensionTwoResolution_isZero_ge_three
        (projectiveResolution X) hX n))
  exact IsZero.of_iso hK (P.isoLeftDerivedObj F (n+3))

theorem projectiveDimension_ge_three_of_nonzero_leftDerived_three
    (F : C ⥤ D) [F.Additive] (h : ¬ IsZero ((F.leftDerived 3).obj X)) :
    (3 : WithBot ℕ∞) ≤ projectiveDimension X := by
  apply (projectiveDimension_ge_iff X 3).mpr
  intro hX
  exact h (leftDerived_isZero_of_projectiveDimensionLE_two F hX 0)

end ASGinzburg
