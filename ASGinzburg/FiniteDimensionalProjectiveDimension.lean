import ASGinzburg.FiniteVertexFiltration
import ASGinzburg.ASLeftExtReciprocity
import ASGinzburg.ASResolutionExtBounds
import Mathlib.CategoryTheory.Abelian.Projective.Dimension

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem rightSimple_hasProjectiveDimensionLE (hAS : A.ASRegular Q) (i : ℤ) :
    HasProjectiveDimensionLE (A.simpleRightModule i) 3 := by
  apply HasProjectiveDimensionLT.mk
  intro n hn N e
  obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 4 m] at hm
  subst n
  obtain ⟨w,rfl⟩ := Q.height_bijective.surjective i
  exact (hAS.resolution A Q w).ext_ge_four_eq_zero N m e

theorem leftSimple_hasProjectiveDimensionLE (hAS : A.ASRegular Q) (i : ℤ) :
    HasProjectiveDimensionLE (A.simpleLeftModule i) 3 := by
  apply HasProjectiveDimensionLT.mk
  intro n hn N e
  obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 4 m] at hm
  subst n
  obtain ⟨u,rfl⟩ := Q.height_bijective.surjective i
  have H := (hAS.resolution A Q (Q.tau u)).leftExt_ge_four_eq_zero hAS N m
  rw [Q.tau.symm_apply_apply] at H
  exact H e

theorem rightVertexFiltration_hasProjectiveDimensionLE (hAS : A.ASRegular Q)
    {M : A.RightModule} (F : A.RightVertexFiltration M) : HasProjectiveDimensionLE M 3 := by
  induction F with
  | @zero M hM =>
    letI : HasProjectiveDimensionLT M 0 := hM.hasProjectiveDimensionLT_zero
    exact hasProjectiveDimensionLT_of_ge M 0 4 (Nat.zero_le _)
  | @step M i f hf tail ih =>
    letI := hf
    have hS : (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
      { exact := ShortComplex.exact_cokernel f }
    exact hS.hasProjectiveDimensionLT_X₂ 4 (A.rightSimple_hasProjectiveDimensionLE Q hAS i) ih

theorem leftVertexFiltration_hasProjectiveDimensionLE (hAS : A.ASRegular Q)
    {M : A.LeftModule} (F : A.LeftVertexFiltration M) : HasProjectiveDimensionLE M 3 := by
  induction F with
  | @zero M hM =>
    letI : HasProjectiveDimensionLT M 0 := hM.hasProjectiveDimensionLT_zero
    exact hasProjectiveDimensionLT_of_ge M 0 4 (Nat.zero_le _)
  | @step M i f hf tail ih =>
    letI := hf
    have hS : (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
      { exact := ShortComplex.exact_cokernel f }
    exact hS.hasProjectiveDimensionLT_X₂ 4 (A.leftSimple_hasProjectiveDimensionLE Q hAS i) ih

theorem rightFiniteDimensional_hasProjectiveDimensionLE (hAS : A.ASRegular Q)
    (M : A.RightModule) (hM : A.rightFiniteDimensionalProperty M) : HasProjectiveDimensionLE M 3 :=
  A.rightVertexFiltration_hasProjectiveDimensionLE Q hAS (A.rightFiniteDimensionalVertexFiltration M hM)

theorem leftFiniteDimensional_hasProjectiveDimensionLE (hAS : A.ASRegular Q)
    (M : A.LeftModule) (hM : A.leftFiniteDimensionalProperty M) : HasProjectiveDimensionLE M 3 :=
  A.leftVertexFiltration_hasProjectiveDimensionLE Q hAS (A.leftFiniteDimensionalVertexFiltration M hM)
end ASGinzburg.ZAlgebra

namespace CategoryTheory.ProjectiveResolution
open CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] {M : C}
  (P : ProjectiveResolution M)

theorem thirdSyzygy_projective (hM : HasProjectiveDimensionLE M 3) :
    Projective (kernel P.secondCover) := by
  have h₁ : HasProjectiveDimensionLT (kernel (P.π.f 0)) 3 :=
    P.shortExact₀.hasProjectiveDimensionLT_X₁ 3 inferInstance hM
  have h₂ : HasProjectiveDimensionLT (kernel P.firstCover) 2 :=
    P.shortExact₁.hasProjectiveDimensionLT_X₁ 2 inferInstance h₁
  have h₃ : HasProjectiveDimensionLT (kernel P.secondCover) 1 :=
    (ShortComplex.ShortExact.mk (ShortComplex.exact_kernel P.secondCover)).hasProjectiveDimensionLT_X₁
      1 inferInstance h₂
  letI := h₃
  exact (projective_iff_hasProjectiveDimensionLT_one _).mpr h₃
end CategoryTheory.ProjectiveResolution
