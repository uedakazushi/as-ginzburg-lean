import work.ASGinzburgDraft.ASCutOrdinaryResolutionMinimality
import work.ASGinzburgDraft.IdealQuotientAnnihilation
import ASGinzburg.ASCutGradedRadicalQuotient
import ASGinzburg.BalancedTensorTorMinimalResolution

/-! Actual first-factor Tor of an AS vertex simple against the genuine
graded radical quotient is the tensor of each minimal resolution term.
The original AS condition also gives vanishing in all degrees at least four. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def ASRegular.cutOrdinarySimpleTorRadicalQuotientIso
    (hAS : A.ASRegular Q) (x : Q.LiftVertex) (n : ℕ) :
    (balancedTensorTorLeftFunctor.{u,v,v,v} k (hAS.CutGradedAlgebra A Q)
      (hAS.CutGradedAlgebra A Q ⧸ hAS.cutGradedRadical A Q) n).obj
        (hAS.cutOrdinarySimple A Q x) ≅
      (balancedTensorLeftFunctor.{u,v,v,v} k (hAS.CutGradedAlgebra A Q)
        (hAS.CutGradedAlgebra A Q ⧸ hAS.cutGradedRadical A Q)).obj
          ((hAS.cutOrdinarySimpleProjectiveResolution A Q x).complex.X n) :=
  balancedTensorTorMinimalResolutionIso k (hAS.CutGradedAlgebra A Q)
    (hAS.CutGradedAlgebra A Q ⧸ hAS.cutGradedRadical A Q)
    (hAS.cutOrdinarySimple A Q x)
    (hAS.cutOrdinarySimpleProjectiveResolution A Q x)
    (hAS.cutGradedRadical A Q)
    (idealQuotient_smul_eq_zero (hAS.CutGradedAlgebra A Q)
      (hAS.cutGradedRadical A Q))
    (hAS.cutOrdinarySimpleProjectiveResolution_minimal A Q x) n

theorem ASRegular.cutOrdinarySimpleTorRadicalQuotient_isZero_ge_four
    (hAS : A.ASRegular Q) (x : Q.LiftVertex) (n : ℕ) :
    IsZero ((balancedTensorTorLeftFunctor.{u,v,v,v} k (hAS.CutGradedAlgebra A Q)
      (hAS.CutGradedAlgebra A Q ⧸ hAS.cutGradedRadical A Q) (n+4)).obj
        (hAS.cutOrdinarySimple A Q x)) :=
  balancedTensorTorLeft_isZero_of_resolution_term k (hAS.CutGradedAlgebra A Q)
    (hAS.CutGradedAlgebra A Q ⧸ hAS.cutGradedRadical A Q)
    (hAS.cutOrdinarySimple A Q x)
    (hAS.cutOrdinarySimpleProjectiveResolution A Q x) (n+4)
    (hAS.cutOrdinarySimpleProjectiveResolution_isZero_ge_four A Q x n)

end ASGinzburg.ZAlgebra
