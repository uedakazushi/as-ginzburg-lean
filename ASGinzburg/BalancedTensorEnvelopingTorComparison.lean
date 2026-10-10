import ASGinzburg.BalancedTensorEnvelopingTotalComparison
import ASGinzburg.AlgebraEnvelopingTensorResolution
import ASGinzburg.BalancedTensorDoubleResolutionTor

/-! The actual enveloping Tor comparison in every degree. Its proof
uses a genuine tensor projective resolution over the enveloping algebra,
the natural total chain isomorphism, and genuine exactness of the
projective first-factor balanced tensor rows. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ModuleCat.Algebra
universe u v w
set_option maxHeartbeats 800000
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable {M : ModuleCat.{max v w} Rᵐᵒᵖ} {N : ModuleCat.{max v w} R}
variable (P : ProjectiveResolution M) (Q : ProjectiveResolution N)

attribute [local instance] regularEnvelopingModule regularEnvelopingScalarTower

noncomputable def balancedTensorEnvelopingTorComparisonIso (n : ℕ) :
    (balancedTensorTorLeftFunctor.{u,v,v,w} k (AlgebraEnvelopingRing k R) R n).obj
        (((tensorRightEnvelopingBifunctor k R).obj M).obj N) ≅
      (balancedTensorTorLeftFunctor.{u,v,max v w,w} k R N n).obj M :=
  balancedTensorTorLeftResolutionIso.{u,v,v,w} k (AlgebraEnvelopingRing k R) R
    (((tensorRightEnvelopingBifunctor k R).obj M).obj N)
    (tensorRightEnvelopingResolution k R P Q) n ≪≫
  (homologyFunctor (ModuleCat.{max v w} k) (ComplexShape.down ℕ) n).mapIso
    (balancedTensorEnvelopingTotalIso k R P.complex Q.complex) ≪≫
  balancedTensorDoubleResolutionTorLeftIso k R P Q n

include Q in
theorem balancedTensorEnvelopingTor_isZero_of_resolution_term
    (n : ℕ) (hP : IsZero (P.complex.X n)) :
    IsZero ((balancedTensorTorLeftFunctor.{u,v,v,w} k
      (AlgebraEnvelopingRing k R) R n).obj
        (((tensorRightEnvelopingBifunctor k R).obj M).obj N)) :=
  IsZero.of_iso (balancedTensorTorLeft_isZero_of_resolution_term k R N M P n hP)
    (balancedTensorEnvelopingTorComparisonIso k R P Q n)

end ASGinzburg
