import ASGinzburg.FiniteProjectiveResolutionLength
import ASGinzburg.FiniteVertexFiltration
import ASGinzburg.ASFiniteProjectiveComplex
import ASGinzburg.ASLeftResolution

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem rightSimple_hasFiniteProjectiveResolutionLength (hAS : A.ASRegular Q) (i : ℤ) :
    A.HasRightFiniteProjectiveResolutionLength 3 (A.simpleRightModule i) := by
  obtain ⟨w,rfl⟩ := Q.height_bijective.surjective i
  let R := hAS.resolution A Q w
  apply A.hasRightFiniteProjectiveResolutionLength_of_fourTermResolution R.toProjectiveResolution
    (R.complex_isZero_ge_four 0)
  intro n _
  exact R.complexTermFiniteProjective n

theorem leftSimple_hasFiniteProjectiveResolutionLength (hAS : A.ASRegular Q) (i : ℤ) :
    A.HasLeftFiniteProjectiveResolutionLength 3 (A.simpleLeftModule i) := by
  obtain ⟨u,rfl⟩ := Q.height_bijective.surjective i
  let R := hAS.resolution A Q (Q.tau u)
  have H := A.hasLeftFiniteProjectiveResolutionLength_of_fourTermResolution
    (R.toLeftProjectiveResolution hAS) (R.leftResolutionComplex_isZero_ge_four 0)
    (fun n _ => R.leftResolutionTermFiniteProjective n)
  rw [Q.tau.symm_apply_apply] at H
  exact H

theorem rightVertexFiltration_hasFiniteProjectiveResolutionLength (hAS : A.ASRegular Q)
    {M : A.RightModule} (F : A.RightVertexFiltration M) :
    A.HasRightFiniteProjectiveResolutionLength 3 M := by
  induction F with
  | zero hM => exact A.hasRightFiniteProjectiveResolutionLength_of_isZero 3 hM
  | @step M i f hf tail ih =>
    letI := hf
    have hS : (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
      { exact := ShortComplex.exact_cokernel f }
    exact A.hasRightFiniteProjectiveResolutionLength_of_shortExact 3 hS
      (A.rightSimple_hasFiniteProjectiveResolutionLength Q hAS i) ih

theorem leftVertexFiltration_hasFiniteProjectiveResolutionLength (hAS : A.ASRegular Q)
    {M : A.LeftModule} (F : A.LeftVertexFiltration M) :
    A.HasLeftFiniteProjectiveResolutionLength 3 M := by
  induction F with
  | zero hM => exact A.hasLeftFiniteProjectiveResolutionLength_of_isZero 3 hM
  | @step M i f hf tail ih =>
    letI := hf
    have hS : (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
      { exact := ShortComplex.exact_cokernel f }
    exact A.hasLeftFiniteProjectiveResolutionLength_of_shortExact 3 hS
      (A.leftSimple_hasFiniteProjectiveResolutionLength Q hAS i) ih

theorem rightFiniteDimensional_hasFiniteProjectiveResolutionLength (hAS : A.ASRegular Q)
    (M : A.RightModule) (hM : A.rightFiniteDimensionalProperty M) :
    A.HasRightFiniteProjectiveResolutionLength 3 M :=
  A.rightVertexFiltration_hasFiniteProjectiveResolutionLength Q hAS
    (A.rightFiniteDimensionalVertexFiltration M hM)

theorem leftFiniteDimensional_hasFiniteProjectiveResolutionLength (hAS : A.ASRegular Q)
    (M : A.LeftModule) (hM : A.leftFiniteDimensionalProperty M) :
    A.HasLeftFiniteProjectiveResolutionLength 3 M :=
  A.leftVertexFiltration_hasFiniteProjectiveResolutionLength Q hAS
    (A.leftFiniteDimensionalVertexFiltration M hM)
end ASGinzburg.ZAlgebra
