import ASGinzburg.PeriodCutEnvelopingAugmentationKernelSpan
import ASGinzburg.PeriodCutEnvelopingVertexIdempotents
import ASGinzburg.IdealActionOperatorSpan

/-! On every genuine enveloping module, the actual augmentation ideal's
action span equals the action span of the proven zero-kernel and positive
homogeneous operators. This supplies actual radical data, rather than a
new radical-span hypothesis, for graded Nakayama. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v w
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices : ℤ))
attribute [local instance 2000] cutEnvelopingOppositeFactorScalarTower
  cutEnvelopingOppositeFactorScalarComm cutGradedRingSelfScalarTower cutGradedRingSelfScalarComm
variable (M : Type w) [AddCommGroup M] [Module k M]
  [Module (AlgebraEnvelopingRing k
    (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))) M]
  [IsScalarTower k (AlgebraEnvelopingRing k
    (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))) M]

theorem cutEnvelopingAugmentationKernel_moduleActionSpan_eq_operators :
    ordinaryIdealActionSpan k
      (AlgebraEnvelopingRing k (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ))))
      M (E.cutEnvelopingAugmentationKernel Q) =
    ordinaryOperatorActionSpan k
      (AlgebraEnvelopingRing k (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ))))
      M (E.cutEnvelopingZeroKernelOperators Q ∪
        E.cutEnvelopingPositiveHomogeneousOperators Q) := by
  apply ordinaryIdealActionSpan_eq_operatorActionSpan
  intro r
  change r ∈ E.cutEnvelopingAugmentationKernelSubspace Q ↔ _
  rw [E.cutEnvelopingAugmentationKernelSubspace_eq_operatorSpan Q]

end ASGinzburg.ZAlgebra.PeriodIso
