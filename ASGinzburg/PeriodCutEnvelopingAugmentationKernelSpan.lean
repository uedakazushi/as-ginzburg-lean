import ASGinzburg.PeriodCutEnvelopingAugmentationKernelDecomposition
import Mathlib.LinearAlgebra.Span.Basic

/-! The full genuine augmentation kernel is exactly the scalar span of
the actual zero-kernel images and the positive homogeneous operators. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices : ℤ))

noncomputable def cutEnvelopingZeroKernelOperators :
    Set (AlgebraEnvelopingRing k (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))) :=
  E.cutEnvelopingZeroInclusion Q ''
    (algebraEnvelopingMapKernel k (E.cutZeroDiagonalAlgHom Q) : Set _)

noncomputable def cutEnvelopingPositiveHomogeneousOperators :
    Set (AlgebraEnvelopingRing k (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))) :=
  ⋃ n : {n : ℕ // 0 < n},
    (E.cutEnvelopingHomogeneousSubspace (fun i : Q.Vertex => (i.val : ℤ)) n.val : Set _)

set_option synthInstance.maxHeartbeats 200000 in
theorem cutEnvelopingZeroKernelOperators_span :
    Submodule.span k (E.cutEnvelopingZeroKernelOperators Q) =
      E.cutEnvelopingAugmentationZeroKernelImage Q := by
  change Submodule.span k
    ((E.cutEnvelopingZeroInclusion Q).toLinearMap ''
      (LinearMap.ker (algebraEnvelopingMap k (E.cutZeroDiagonalAlgHom Q)).toLinearMap : Set _)) = _
  rw [← Submodule.map_span, Submodule.span_eq]
  rfl

theorem cutEnvelopingPositiveHomogeneousOperators_span :
    Submodule.span k (E.cutEnvelopingPositiveHomogeneousOperators Q) =
      E.cutEnvelopingPositiveHomogeneousSubspace Q := by
  unfold cutEnvelopingPositiveHomogeneousOperators cutEnvelopingPositiveHomogeneousSubspace
  simp only [Submodule.span_iUnion, Submodule.span_eq]

theorem cutEnvelopingAugmentationKernelSubspace_eq_operatorSpan :
    E.cutEnvelopingAugmentationKernelSubspace Q =
      Submodule.span k (E.cutEnvelopingZeroKernelOperators Q ∪
        E.cutEnvelopingPositiveHomogeneousOperators Q) := by
  rw [Submodule.span_union, E.cutEnvelopingZeroKernelOperators_span Q,
    E.cutEnvelopingPositiveHomogeneousOperators_span Q,
    E.cutEnvelopingAugmentationKernelSubspace_eq_zero_sup_positive Q]

end ASGinzburg.ZAlgebra.PeriodIso
