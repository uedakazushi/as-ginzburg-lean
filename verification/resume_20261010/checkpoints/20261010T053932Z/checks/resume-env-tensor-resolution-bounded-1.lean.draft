import work.ASGinzburgDraft.AlgebraEnvelopingTensorResolution
import work.ASGinzburgDraft.BifunctorTotalBounded

/-! The actual enveloping tensor resolution is bounded by the sum of
the actual bounds of the ordinary factor projective resolutions. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable {M : ModuleCat.{w} Rᵐᵒᵖ} {N : ModuleCat.{z} R}
variable (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
variable [Small.{w} Rᵐᵒᵖ] [Small.{z} R]

theorem tensorRightEnvelopingResolution_isZero (a b : ℕ)
    (hP : ∀ i, a < i → IsZero (P.complex.X i))
    (hQ : ∀ j, b < j → IsZero (Q.complex.X j)) (n : ℕ) (hn : a + b < n) :
    IsZero ((tensorRightEnvelopingResolution k R P Q).complex.X n) :=
  bifunctorTotal_isZero_of_bounded P.complex Q.complex
    (tensorRightEnvelopingBifunctor k R) a b hP hQ n hn

end ASGinzburg
