import ASGinzburg.ASCutOrdinaryTopTensorNonzero
import ASGinzburg.ASCutOrdinaryTorMinimalResolution
import ASGinzburg.ASCutOrdinarySimpleDimension
import ASGinzburg.ProjectiveDimensionTwoDerivedVanishing

/-! Original AS conditions imply the sharp projective dimension three
of every ordinary cut vertex simple. The lower bound uses actual nonzero
third Tor, computed from the genuine minimal four-term resolution. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem ASRegular.cutOrdinarySimpleTorRadicalQuotient_three_not_isZero
    (hAS : A.ASRegular Q) (x : Q.LiftVertex) :
    ¬ IsZero ((balancedTensorTorLeftFunctor.{u,v,v,v} k (hAS.CutGradedAlgebra A Q)
      (hAS.CutGradedAlgebra A Q ⧸ hAS.cutGradedRadical A Q) 3).obj
        (hAS.cutOrdinarySimple A Q x)) := by
  intro h
  exact hAS.cutOrdinarySimpleTopTensor_not_isZero A Q x
    (IsZero.of_iso h (hAS.cutOrdinarySimpleTorRadicalQuotientIso A Q x 3).symm)

theorem ASRegular.cutOrdinarySimple_projectiveDimension_ge_three
    (hAS : A.ASRegular Q) (x : Q.LiftVertex) :
    (3 : WithBot ℕ∞) ≤ projectiveDimension (hAS.cutOrdinarySimple A Q x) :=
  projectiveDimension_ge_three_of_nonzero_leftDerived_three
    (balancedTensorLeftFunctor.{u,v,v,v} k (hAS.CutGradedAlgebra A Q)
      (hAS.CutGradedAlgebra A Q ⧸ hAS.cutGradedRadical A Q))
    (hAS.cutOrdinarySimpleTorRadicalQuotient_three_not_isZero A Q x)

theorem ASRegular.cutOrdinarySimple_projectiveDimension_eq_three
    (hAS : A.ASRegular Q) (x : Q.LiftVertex) :
    projectiveDimension (hAS.cutOrdinarySimple A Q x) = 3 :=
  le_antisymm ((projectiveDimension_le_iff _ 3).mpr inferInstance)
    (hAS.cutOrdinarySimple_projectiveDimension_ge_three A Q x)

end ASGinzburg.ZAlgebra
