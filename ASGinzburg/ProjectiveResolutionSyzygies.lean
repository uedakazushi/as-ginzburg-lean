import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Exact

namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
universe u v t
variable {C : Type u} [Category.{v} C] [Abelian C] {X : C}

theorem exact_comp_mono_iff {X Y Z W : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (e : Z ⟶ W) [Mono e] (h : f ≫ g = 0) :
    (ShortComplex.mk f g h).Exact ↔
      (ShortComplex.mk f (g ≫ e) (by rw [← Category.assoc, h, zero_comp])).Exact := by
  let φ : ShortComplex.mk f g h ⟶
      ShortComplex.mk f (g ≫ e) (by rw [← Category.assoc, h, zero_comp]) :=
    { τ₁ := 𝟙 X, τ₂ := 𝟙 Y, τ₃ := e }
  haveI : Epi φ.τ₁ := by dsimp [φ]; infer_instance
  haveI : IsIso φ.τ₂ := by dsimp [φ]; infer_instance
  haveI : Mono φ.τ₃ := by dsimp [φ]; infer_instance
  exact ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ

end ASGinzburg

namespace CategoryTheory.ProjectiveResolution
open CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] {X : C}
variable (P : CategoryTheory.ProjectiveResolution X)

noncomputable def firstCover : P.complex.X 1 ⟶ kernel (P.π.f 0) :=
  kernel.lift _ (P.complex.d 1 0) P.complex_d_comp_π_f_zero

@[simp] theorem firstCover_ι : P.firstCover ≫ kernel.ι (P.π.f 0) = P.complex.d 1 0 :=
  kernel.lift_ι _ _ _

noncomputable instance firstCoverEpi : Epi P.firstCover :=
  (ShortComplex.exact_iff_epi_kernel_lift
    (ShortComplex.mk _ _ P.complex_d_comp_π_f_zero)).mp P.exact₀

theorem d₂_firstCover : P.complex.d 2 1 ≫ P.firstCover = 0 := by
  rw [← cancel_mono (kernel.ι (P.π.f 0)), Category.assoc, P.firstCover_ι,
    P.complex.d_comp_d, zero_comp]

theorem exact_d₂_firstCover :
    (ShortComplex.mk (P.complex.d 2 1) P.firstCover P.d₂_firstCover).Exact := by
  apply (ASGinzburg.exact_comp_mono_iff _ _ (kernel.ι (P.π.f 0)) P.d₂_firstCover).mpr
  simpa only [P.firstCover_ι] using P.exact_succ 0

noncomputable def secondCover : P.complex.X 2 ⟶ kernel P.firstCover :=
  kernel.lift _ (P.complex.d 2 1) P.d₂_firstCover

@[simp] theorem secondCover_ι : P.secondCover ≫ kernel.ι P.firstCover = P.complex.d 2 1 :=
  kernel.lift_ι _ _ _

noncomputable instance secondCoverEpi : Epi P.secondCover :=
  (ShortComplex.exact_iff_epi_kernel_lift
    (ShortComplex.mk _ _ P.d₂_firstCover)).mp P.exact_d₂_firstCover

theorem d₃_secondCover : P.complex.d 3 2 ≫ P.secondCover = 0 := by
  rw [← cancel_mono (kernel.ι P.firstCover), Category.assoc, P.secondCover_ι,
    P.complex.d_comp_d, zero_comp]

theorem exact_d₃_secondCover :
    (ShortComplex.mk (P.complex.d 3 2) P.secondCover P.d₃_secondCover).Exact := by
  apply (ASGinzburg.exact_comp_mono_iff _ _ (kernel.ι P.firstCover) P.d₃_secondCover).mpr
  simpa only [P.secondCover_ι] using P.exact_succ 1

theorem shortExact₀ :
    (ShortComplex.mk (kernel.ι (P.π.f 0)) (P.π.f 0) (kernel.condition _)).ShortExact where
  exact := ShortComplex.exact_kernel _

theorem shortExact₁ :
    (ShortComplex.mk (kernel.ι P.firstCover) P.firstCover (kernel.condition _)).ShortExact where
  exact := ShortComplex.exact_kernel _
  epi_g := P.firstCoverEpi

theorem mono_d₃_of_isZero_four (h₄ : IsZero (P.complex.X 4)) : Mono (P.complex.d 3 2) :=
  (ShortComplex.exact_iff_mono _ (h₄.eq_of_src _ _)).mp (P.exact_succ 2)

theorem shortExact₂ (h₄ : IsZero (P.complex.X 4)) :
    (ShortComplex.mk (P.complex.d 3 2) P.secondCover P.d₃_secondCover).ShortExact where
  exact := P.exact_d₃_secondCover
  mono_f := P.mono_d₃_of_isZero_four h₄
  epi_g := P.secondCoverEpi
end CategoryTheory.ProjectiveResolution

