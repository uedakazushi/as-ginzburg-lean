import ASGinzburg.PeriodCutEnvelopingQuotient
import ASGinzburg.ASCutGradedRadicalQuotient

/-! The original AS conditions give the genuine enveloping augmentation
of the native cut algebra. Its actual two-sided kernel quotient is the
enveloping algebra of the graded-radical quotient, hence a finite product
of fields. No enveloping resolution or global-dimension bound is assumed. -/
namespace ASGinzburg.ZAlgebra
open scoped TensorProduct
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def ASRegular.cutEnvelopingAugmentation (hAS : A.ASRegular Q) :
    AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q) →ₐ[k]
      AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q ⧸ hAS.cutGradedRadical A Q) :=
  (hAS.periodIso A Q).cutEnvelopingAugmentation Q

theorem ASRegular.cutEnvelopingAugmentation_tmul (hAS : A.ASRegular Q)
    (a b : hAS.CutGradedAlgebra A Q) :
    hAS.cutEnvelopingAugmentation A Q (a ⊗ₜ[k] MulOpposite.op b) =
      Ideal.Quotient.mk (hAS.cutGradedRadical A Q) a ⊗ₜ[k]
        MulOpposite.op (Ideal.Quotient.mk (hAS.cutGradedRadical A Q) b) := rfl

theorem ASRegular.cutEnvelopingAugmentation_surjective (hAS : A.ASRegular Q) :
    Function.Surjective (hAS.cutEnvelopingAugmentation A Q) :=
  (hAS.periodIso A Q).cutEnvelopingAugmentation_surjective Q

noncomputable def ASRegular.cutEnvelopingAugmentationKernel (hAS : A.ASRegular Q) :
    Ideal (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q)) :=
  (hAS.periodIso A Q).cutEnvelopingAugmentationKernel Q

noncomputable instance ASRegular.cutEnvelopingAugmentationKernelTwoSided
    (hAS : A.ASRegular Q) :
    (hAS.cutEnvelopingAugmentationKernel A Q).IsTwoSided :=
  (hAS.periodIso A Q).cutEnvelopingAugmentationKernelTwoSided Q

abbrev ASRegular.CutEnvelopingAugmentationQuotient (hAS : A.ASRegular Q) :=
  (hAS.periodIso A Q).CutEnvelopingAugmentationQuotient Q

theorem ASRegular.mem_cutEnvelopingAugmentationKernel (hAS : A.ASRegular Q)
    (x : AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q)) :
    x ∈ hAS.cutEnvelopingAugmentationKernel A Q ↔
      hAS.cutEnvelopingAugmentation A Q x = 0 := Iff.rfl

noncomputable def ASRegular.cutEnvelopingAugmentationQuotientAlgEquiv
    (hAS : A.ASRegular Q) :
    hAS.CutEnvelopingAugmentationQuotient A Q ≃ₐ[k]
        AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q ⧸ hAS.cutGradedRadical A Q) :=
  (hAS.periodIso A Q).cutEnvelopingAugmentationQuotientAlgEquiv Q

noncomputable def ASRegular.cutEnvelopingAugmentationQuotientScalarAlgEquiv
    (hAS : A.ASRegular Q) :
    hAS.CutEnvelopingAugmentationQuotient A Q ≃ₐ[k] (Q.Vertex → Q.Vertex → k) :=
  (hAS.periodIso A Q).cutEnvelopingAugmentationQuotientScalarAlgEquiv Q

theorem ASRegular.cutEnvelopingAugmentationQuotient_isSemisimple
    (hAS : A.ASRegular Q) :
    IsSemisimpleRing (hAS.CutEnvelopingAugmentationQuotient A Q) :=
  (hAS.periodIso A Q).cutEnvelopingAugmentationQuotient_isSemisimple Q

end ASGinzburg.ZAlgebra
