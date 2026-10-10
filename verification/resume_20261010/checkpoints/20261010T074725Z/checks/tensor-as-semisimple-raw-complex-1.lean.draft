import work.ASGinzburgDraft.ASCutSemisimpleRingDualTensorComplex
import work.ASGinzburgDraft.ASCutSemisimpleLeftTensorFieldComparison

/-! The actual reduced enveloping ring-Hom complex is exact precisely
when reduction by the raw semisimple quotient is exact. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory Opposite
open scoped ModuleCat.Algebra
universe u v t
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def ASRegular.cutEnvelopingRingDualRawSemisimpleTensorFunctor
    (hAS : A.ASRegular Q) :
    (ModuleCat.{v} (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q)))ᵒᵖ ⥤
      ModuleCat.{v} k :=
  ordinaryRingDualFunctor (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q)) ⋙
    rightEnvelopingRightRestrictionFunctor k (hAS.CutGradedAlgebra A Q) ⋙
      balancedTensorLeftFunctor k (hAS.CutGradedAlgebra A Q)
        (hAS.CutGradedAlgebra A Q ⧸ hAS.cutGradedRadical A Q)

instance ASRegular.cutEnvelopingRingDualRawSemisimpleTensorFunctorPreservesZero
    (hAS : A.ASRegular Q) :
    (hAS.cutEnvelopingRingDualRawSemisimpleTensorFunctor A Q).PreservesZeroMorphisms := by
  unfold cutEnvelopingRingDualRawSemisimpleTensorFunctor
    rightEnvelopingRightRestrictionFunctor
  infer_instance

set_option maxHeartbeats 1000000 in
noncomputable def ASRegular.cutEnvelopingRingDualLeftRawSemisimpleTensorIso
    (hAS : A.ASRegular Q) :
    hAS.cutEnvelopingRingDualSemisimpleLeftTensorFunctor A Q ≅
      hAS.cutEnvelopingRingDualRawSemisimpleTensorFunctor A Q := by
  let R := hAS.CutGradedAlgebra A Q
  let F := ordinaryRingDualFunctor (AlgebraEnvelopingRing k R) ⋙
    rightEnvelopingRightRestrictionFunctor k R
  exact Functor.isoWhiskerLeft F (hAS.cutSemisimpleLeftTensorRawFieldIso A Q)

set_option maxHeartbeats 1000000 in
theorem ASRegular.cutEnvelopingRingDualRawSemisimpleTensor_exactAt_iff
    (hAS : A.ASRegular Q) {ι : Type t} {c : ComplexShape ι}
    (K : HomologicalComplex
      (ModuleCat.{v} (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))) c) (i : ι) :
    (((envelopingRingDualTensorEvaluationSourceFunctor k (hAS.CutGradedAlgebra A Q)
      (hAS.cutSemisimpleRightObject A Q)).mapHomologicalComplex c.symm).obj K.op).ExactAt i ↔
      (((hAS.cutEnvelopingRingDualRawSemisimpleTensorFunctor A Q).mapHomologicalComplex
        c.symm).obj K.op).ExactAt i := by
  rw [hAS.cutEnvelopingRingDualSemisimpleTensor_exactAt_iff A Q K i]
  let e := (NatIso.mapHomologicalComplex
    (hAS.cutEnvelopingRingDualLeftRawSemisimpleTensorIso A Q) c.symm).app K.op
  exact ⟨fun h => h.of_iso e, fun h => h.of_iso e.symm⟩

end ASGinzburg.ZAlgebra
