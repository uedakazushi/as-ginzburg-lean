import work.ASGinzburgDraft.AlgebraEnvelopingQuotient
import work.ASGinzburgDraft.PeriodCutEnvelopingScalars
import ASGinzburg.PeriodCutGradedJacobson
import ASGinzburg.ScalarProductSeparability

/-! The genuine enveloping augmentation of the cut algebra onto the
enveloping algebra of its actual graded-radical quotient. Its two-sided
kernel has a genuinely semisimple quotient. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open scoped TensorProduct
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices : ℤ))

noncomputable def cutEnvelopingAugmentation :
    AlgebraEnvelopingRing k (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ))) →ₐ[k]
      AlgebraEnvelopingRing k
        (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)) ⧸ E.cutGradedJacobson Q) :=
  algebraEnvelopingQuotientAugmentation k _ (E.cutGradedJacobson Q)

theorem cutEnvelopingAugmentation_surjective :
    Function.Surjective (E.cutEnvelopingAugmentation Q) :=
  algebraEnvelopingQuotientAugmentation_surjective k _ (E.cutGradedJacobson Q)

noncomputable def cutEnvelopingAugmentationKernel :=
  algebraEnvelopingQuotientKernel k _ (E.cutGradedJacobson Q)

noncomputable instance cutEnvelopingAugmentationKernelTwoSided :
    (E.cutEnvelopingAugmentationKernel Q).IsTwoSided := by
  unfold cutEnvelopingAugmentationKernel
  infer_instance

theorem mem_cutEnvelopingAugmentationKernel
    (x : AlgebraEnvelopingRing k (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))) :
    x ∈ E.cutEnvelopingAugmentationKernel Q ↔ E.cutEnvelopingAugmentation Q x = 0 := Iff.rfl

noncomputable def cutEnvelopingAugmentationQuotientAlgEquiv :
    (AlgebraEnvelopingRing k (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ))) ⧸
      E.cutEnvelopingAugmentationKernel Q) ≃ₐ[k]
        AlgebraEnvelopingRing k
          (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)) ⧸ E.cutGradedJacobson Q) :=
  algebraEnvelopingQuotientAlgEquiv k _ (E.cutGradedJacobson Q)

noncomputable def cutEnvelopingAugmentationQuotientScalarAlgEquiv :
    (AlgebraEnvelopingRing k (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ))) ⧸
      E.cutEnvelopingAugmentationKernel Q) ≃ₐ[k] (Q.Vertex → Q.Vertex → k) :=
  (E.cutEnvelopingAugmentationQuotientAlgEquiv Q).trans
    ((Algebra.TensorProduct.congr (E.cutGradedSemisimpleQuotientAlgEquiv Q)
      (E.cutGradedSemisimpleQuotientAlgEquiv Q).op).trans
        (scalarProductEnvelopingEquiv k Q.Vertex))

theorem cutEnvelopingAugmentationQuotient_isSemisimple :
    IsSemisimpleRing
      (AlgebraEnvelopingRing k (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ))) ⧸
        E.cutEnvelopingAugmentationKernel Q) :=
  (E.cutEnvelopingAugmentationQuotientScalarAlgEquiv Q).symm.toRingEquiv.isSemisimpleRing

end ASGinzburg.ZAlgebra.PeriodIso
