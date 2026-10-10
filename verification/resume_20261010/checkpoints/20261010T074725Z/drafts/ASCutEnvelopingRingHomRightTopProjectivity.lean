import work.ASGinzburgDraft.ModuleCatCochainTopCokernelIso
import work.ASGinzburgDraft.ASCutEnvelopingRingHomRightConcentration

/-! Original AS regularity gives projective actual degree-three homology
after first-factor restriction. The same conclusion holds for the actual
derived enveloping ring-dual Ext object with its genuine right action. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u v
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem ASRegular.cutEnvelopingMinimalRingHomRight_homology_three_projective
    (hAS : A.ASRegular Q) :
    Projective ((hAS.cutEnvelopingMinimalRingHomRightNatComplex A Q).homology 3) := by
  let K := hAS.cutEnvelopingMinimalRingHomRightNatComplex A Q
  have hC : Projective (ModuleCat.of (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ
      (K.X 3 ⧸ LinearMap.range (K.d 2 3).hom)) :=
    (hAS.cutEnvelopingMinimalRingHomRight_lowExact_top_projective A Q).2.2.2
  exact Projective.of_iso (moduleCatCochainHomologyThreeIsoTopCokernel K
    (hAS.cutEnvelopingMinimalRingHomRightNatComplex_isZero_ge_four A Q 0)).symm hC

noncomputable def ASRegular.cutEnvelopingMinimalRingHomRightHomologyIso
    (hAS : A.ASRegular Q) (n : ℕ) :
    (hAS.cutEnvelopingMinimalRingHomRightNatComplex A Q).homology n ≅
      (envelopingOppositeLeftRestrictionFunctor k (hAS.CutGradedAlgebra A Q)).obj
        ((hAS.cutEnvelopingMinimalRingHomNatComplex A Q).homology n) :=
  ((hAS.cutEnvelopingMinimalRingHomNatComplex A Q).sc n).mapHomologyIso
    (envelopingOppositeLeftRestrictionFunctor k (hAS.CutGradedAlgebra A Q))

noncomputable def ASRegular.cutEnvelopingRingDualExtRightHomologyIso
    (hAS : A.ASRegular Q) (n : ℕ) :
    (envelopingOppositeLeftRestrictionFunctor k (hAS.CutGradedAlgebra A Q)).obj
        (hAS.cutEnvelopingRingDualExtObject A Q n) ≅
      (hAS.cutEnvelopingMinimalRingHomRightNatComplex A Q).homology n :=
  (envelopingOppositeLeftRestrictionFunctor k (hAS.CutGradedAlgebra A Q)).mapIso
    (hAS.cutEnvelopingMinimalRingDualExtHomologyIso A Q n) ≪≫
      (hAS.cutEnvelopingMinimalRingHomRightHomologyIso A Q n).symm

theorem ASRegular.cutEnvelopingRingDualExt_three_right_projective
    (hAS : A.ASRegular Q) :
    Projective ((envelopingOppositeLeftRestrictionFunctor k
      (hAS.CutGradedAlgebra A Q)).obj (hAS.cutEnvelopingRingDualExtObject A Q 3)) :=
  Projective.of_iso (hAS.cutEnvelopingRingDualExtRightHomologyIso A Q 3).symm
    (hAS.cutEnvelopingMinimalRingHomRight_homology_three_projective A Q)

end ASGinzburg.ZAlgebra
