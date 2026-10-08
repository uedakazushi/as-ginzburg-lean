import ASGinzburg.ASResolution
import ASGinzburg.RightModuleExtSequence

/-!
# Actual syzygy short exact sequences of the finite AS resolution

The kernels and epimorphic lifts below are constructed in the existing
right-module category. Exactness is deduced from the supplied AS sequence.
-/

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

theorem rightModule_exact_comp_mono_iff {X Y Z W : A.RightModule}
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

namespace ASResolution
variable {A} {Q : CutQuiver} {v : Q.LiftVertex} (R : A.ASResolution Q v)

noncomputable def firstCover : A.asResolutionTerm₁ Q v ⟶
    kernel (A.simpleRightModuleπ (Q.height v)) :=
  kernel.lift _ R.d₁ R.d₁_π

@[simp] theorem firstCover_ι :
    R.firstCover ≫ kernel.ι (A.simpleRightModuleπ (Q.height v)) = R.d₁ :=
  kernel.lift_ι _ _ _

noncomputable instance firstCoverEpi : Epi R.firstCover :=
  (ShortComplex.exact_iff_epi_kernel_lift
    (ShortComplex.mk R.d₁ (A.simpleRightModuleπ (Q.height v)) R.d₁_π)).mp R.exact₀

theorem d₂_firstCover : R.d₂ ≫ R.firstCover = 0 := by
  rw [← cancel_mono (kernel.ι (A.simpleRightModuleπ (Q.height v))),
    Category.assoc, R.firstCover_ι, R.d₂_d₁, zero_comp]

theorem exact_d₂_firstCover : (ShortComplex.mk R.d₂ R.firstCover R.d₂_firstCover).Exact := by
  apply (A.rightModule_exact_comp_mono_iff R.d₂ R.firstCover
    (kernel.ι (A.simpleRightModuleπ (Q.height v))) R.d₂_firstCover).mpr
  simpa only [R.firstCover_ι] using R.exact₁

noncomputable def secondCover : A.asResolutionTerm₂ Q v ⟶ kernel R.firstCover :=
  kernel.lift _ R.d₂ R.d₂_firstCover

@[simp] theorem secondCover_ι : R.secondCover ≫ kernel.ι R.firstCover = R.d₂ :=
  kernel.lift_ι _ _ _

noncomputable instance secondCoverEpi : Epi R.secondCover :=
  (ShortComplex.exact_iff_epi_kernel_lift
    (ShortComplex.mk R.d₂ R.firstCover R.d₂_firstCover)).mp R.exact_d₂_firstCover

theorem d₃_secondCover : R.d₃ ≫ R.secondCover = 0 := by
  rw [← cancel_mono (kernel.ι R.firstCover), Category.assoc, R.secondCover_ι,
    R.d₃_d₂, zero_comp]

theorem exact_d₃_secondCover :
    (ShortComplex.mk R.d₃ R.secondCover R.d₃_secondCover).Exact := by
  apply (A.rightModule_exact_comp_mono_iff R.d₃ R.secondCover
    (kernel.ι R.firstCover) R.d₃_secondCover).mpr
  simpa only [R.secondCover_ι] using R.exact₂

theorem shortExact₀ :
    (ShortComplex.mk (kernel.ι (A.simpleRightModuleπ (Q.height v)))
      (A.simpleRightModuleπ (Q.height v)) (kernel.condition _)).ShortExact where
  exact := ShortComplex.exact_kernel _


theorem shortExact₁ :
    (ShortComplex.mk (kernel.ι R.firstCover) R.firstCover (kernel.condition _)).ShortExact where
  exact := ShortComplex.exact_kernel _
  epi_g := R.firstCoverEpi

theorem shortExact₂ :
    (ShortComplex.mk R.d₃ R.secondCover R.d₃_secondCover).ShortExact where
  exact := R.exact_d₃_secondCover
  mono_f := R.mono_d₃
  epi_g := R.secondCoverEpi

end ASResolution
end ASGinzburg.ZAlgebra
