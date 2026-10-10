import ASGinzburg.FourTermProjectiveResolution
import ASGinzburg.FiniteProjectiveResolutionLength

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

theorem exists_rightFiniteProjectiveFourTermResolution {M : A.RightModule}
    (hM : A.HasRightFiniteProjectiveResolutionLength 3 M) :
    ∃ R : ASGinzburg.FourTermProjectiveResolution M,
      ∀ n, A.rightFiniteProjectiveProperty (R.term n) := by
  obtain ⟨P₀,p₀,hP₀,hp₀,P₁,p₁,hP₁,hp₁,P₂,p₂,hP₂,hp₂,hP₃⟩ := hM
  letI := hp₀
  letI := hp₁
  letI := hp₂
  letI : Projective P₀ := A.rightFiniteProjectiveProperty_projective hP₀
  letI : Projective P₁ := A.rightFiniteProjectiveProperty_projective hP₁
  letI : Projective P₂ := A.rightFiniteProjectiveProperty_projective hP₂
  letI : Projective (kernel p₂) := A.rightFiniteProjectiveProperty_projective hP₃
  let R := ASGinzburg.FourTermProjectiveResolution.ofKernelCovers p₀ p₁ p₂
  refine ⟨R,?_⟩
  intro n
  rcases n with _ | _ | _ | _ | n
  · exact hP₀
  · exact hP₁
  · exact hP₂
  · exact hP₃
  · exact A.rightFiniteProjectiveProperty_of_isZero (isZero_zero _)

noncomputable def rightFiniteProjectiveFourTermResolution (M : A.RightModule)
    (hM : A.HasRightFiniteProjectiveResolutionLength 3 M) :
    ASGinzburg.FourTermProjectiveResolution M :=
  (A.exists_rightFiniteProjectiveFourTermResolution hM).choose

theorem rightFiniteProjectiveFourTermResolution_finite (M : A.RightModule)
    (hM : A.HasRightFiniteProjectiveResolutionLength 3 M) (n : ℕ) :
    A.rightFiniteProjectiveProperty ((A.rightFiniteProjectiveFourTermResolution M hM).term n) :=
  (A.exists_rightFiniteProjectiveFourTermResolution hM).choose_spec n

noncomputable def rightFiniteProjectiveProjectiveResolution (M : A.RightModule)
    (hM : A.HasRightFiniteProjectiveResolutionLength 3 M) : ProjectiveResolution M :=
  (A.rightFiniteProjectiveFourTermResolution M hM).toProjectiveResolution

theorem rightFiniteProjectiveProjectiveResolution_finite (M : A.RightModule)
    (hM : A.HasRightFiniteProjectiveResolutionLength 3 M) (n : ℕ) :
    A.rightFiniteProjectiveProperty ((A.rightFiniteProjectiveProjectiveResolution M hM).complex.X n) :=
  A.rightFiniteProjectiveFourTermResolution_finite M hM n

theorem rightFiniteProjectiveProjectiveResolution_isZero_ge_four (M : A.RightModule)
    (hM : A.HasRightFiniteProjectiveResolutionLength 3 M) (n : ℕ) :
    IsZero ((A.rightFiniteProjectiveProjectiveResolution M hM).complex.X (n+4)) :=
  (A.rightFiniteProjectiveFourTermResolution M hM).complex_isZero_ge_four n
end ASGinzburg.ZAlgebra

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

theorem exists_leftFiniteProjectiveFourTermResolution {M : A.LeftModule}
    (hM : A.HasLeftFiniteProjectiveResolutionLength 3 M) :
    ∃ R : ASGinzburg.FourTermProjectiveResolution M,
      ∀ n, A.leftFiniteProjectiveProperty (R.term n) := by
  obtain ⟨P₀,p₀,hP₀,hp₀,P₁,p₁,hP₁,hp₁,P₂,p₂,hP₂,hp₂,hP₃⟩ := hM
  letI := hp₀
  letI := hp₁
  letI := hp₂
  letI : Projective P₀ := A.leftFiniteProjectiveProperty_projective hP₀
  letI : Projective P₁ := A.leftFiniteProjectiveProperty_projective hP₁
  letI : Projective P₂ := A.leftFiniteProjectiveProperty_projective hP₂
  letI : Projective (kernel p₂) := A.leftFiniteProjectiveProperty_projective hP₃
  let R := ASGinzburg.FourTermProjectiveResolution.ofKernelCovers p₀ p₁ p₂
  refine ⟨R,?_⟩
  intro n
  rcases n with _ | _ | _ | _ | n
  · exact hP₀
  · exact hP₁
  · exact hP₂
  · exact hP₃
  · exact A.leftFiniteProjectiveProperty_of_isZero (isZero_zero _)

noncomputable def leftFiniteProjectiveFourTermResolution (M : A.LeftModule)
    (hM : A.HasLeftFiniteProjectiveResolutionLength 3 M) :
    ASGinzburg.FourTermProjectiveResolution M :=
  (A.exists_leftFiniteProjectiveFourTermResolution hM).choose

theorem leftFiniteProjectiveFourTermResolution_finite (M : A.LeftModule)
    (hM : A.HasLeftFiniteProjectiveResolutionLength 3 M) (n : ℕ) :
    A.leftFiniteProjectiveProperty ((A.leftFiniteProjectiveFourTermResolution M hM).term n) :=
  (A.exists_leftFiniteProjectiveFourTermResolution hM).choose_spec n

noncomputable def leftFiniteProjectiveProjectiveResolution (M : A.LeftModule)
    (hM : A.HasLeftFiniteProjectiveResolutionLength 3 M) : ProjectiveResolution M :=
  (A.leftFiniteProjectiveFourTermResolution M hM).toProjectiveResolution

theorem leftFiniteProjectiveProjectiveResolution_finite (M : A.LeftModule)
    (hM : A.HasLeftFiniteProjectiveResolutionLength 3 M) (n : ℕ) :
    A.leftFiniteProjectiveProperty ((A.leftFiniteProjectiveProjectiveResolution M hM).complex.X n) :=
  A.leftFiniteProjectiveFourTermResolution_finite M hM n

theorem leftFiniteProjectiveProjectiveResolution_isZero_ge_four (M : A.LeftModule)
    (hM : A.HasLeftFiniteProjectiveResolutionLength 3 M) (n : ℕ) :
    IsZero ((A.leftFiniteProjectiveProjectiveResolution M hM).complex.X (n+4)) :=
  (A.leftFiniteProjectiveFourTermResolution M hM).complex_isZero_ge_four n
end ASGinzburg.ZAlgebra
