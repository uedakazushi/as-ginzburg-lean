import work.ASGinzburgDraft.PeriodCutEnvelopingInternalGrading
import work.ASGinzburgDraft.PeriodCutEnvelopingAugmentationKernelSpan
import work.ASGinzburgDraft.ASCutEnvelopingQuotient

/-! The original AS condition supplies the actual internal grading of the
ordinary enveloping ring and the exact scalar span of its genuine
augmentation kernel. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def ASRegular.cutEnvelopingHomogeneousSubspace (hAS : A.ASRegular Q) (n : ℕ) :
    Submodule k (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q)) :=
  (hAS.periodIso A Q).cutEnvelopingHomogeneousSubspace (fun i : Q.Vertex => (i.val : ℤ)) n

noncomputable def ASRegular.cutEnvelopingIntegerHomogeneousSubspace
    (hAS : A.ASRegular Q) (q : ℤ) :
    Submodule k (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q)) :=
  (hAS.periodIso A Q).cutEnvelopingIntegerHomogeneousSubspace
    (fun i : Q.Vertex => (i.val : ℤ)) q

noncomputable instance ASRegular.cutEnvelopingHomogeneousDecomposition
    (hAS : A.ASRegular Q) :
    DirectSum.Decomposition (hAS.cutEnvelopingHomogeneousSubspace A Q) :=
  (hAS.periodIso A Q).cutEnvelopingHomogeneousDecomposition (fun i : Q.Vertex => (i.val : ℤ))

noncomputable instance ASRegular.cutEnvelopingIntegerHomogeneousDecomposition
    (hAS : A.ASRegular Q) :
    DirectSum.Decomposition (hAS.cutEnvelopingIntegerHomogeneousSubspace A Q) :=
  (hAS.periodIso A Q).cutEnvelopingIntegerHomogeneousDecomposition
    (fun i : Q.Vertex => (i.val : ℤ))

set_option synthInstance.maxHeartbeats 200000 in
noncomputable instance ASRegular.cutEnvelopingIntegerGradedMonoid
    (hAS : A.ASRegular Q) :
    SetLike.GradedMonoid (hAS.cutEnvelopingIntegerHomogeneousSubspace A Q) :=
  (hAS.periodIso A Q).cutEnvelopingIntegerGradedMonoid Q

theorem ASRegular.cutEnvelopingIntegerHomogeneousSubspace_natCast
    (hAS : A.ASRegular Q) (n : ℕ) :
    hAS.cutEnvelopingIntegerHomogeneousSubspace A Q (n : ℤ) =
      hAS.cutEnvelopingHomogeneousSubspace A Q n :=
  (hAS.periodIso A Q).cutEnvelopingIntegerHomogeneousSubspace_natCast
    (fun i : Q.Vertex => (i.val : ℤ)) n

theorem ASRegular.cutEnvelopingIntegerHomogeneousSubspace_neg
    (hAS : A.ASRegular Q) (q : ℤ) (hq : q < 0) :
    hAS.cutEnvelopingIntegerHomogeneousSubspace A Q q = ⊥ :=
  (hAS.periodIso A Q).cutEnvelopingIntegerHomogeneousSubspace_neg
    (fun i : Q.Vertex => (i.val : ℤ)) q hq

set_option synthInstance.maxHeartbeats 200000 in
theorem ASRegular.cutEnvelopingIntegerHomogeneousSubspace_mul_mem
    (hAS : A.ASRegular Q) (q r : ℤ)
    {x y : AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q)}
    (hx : x ∈ hAS.cutEnvelopingIntegerHomogeneousSubspace A Q q)
    (hy : y ∈ hAS.cutEnvelopingIntegerHomogeneousSubspace A Q r) :
    x*y ∈ hAS.cutEnvelopingIntegerHomogeneousSubspace A Q (q+r) :=
  (hAS.periodIso A Q).cutEnvelopingIntegerHomogeneousSubspace_mul_mem
    (fun i : Q.Vertex => (i.val : ℤ)) q r hx hy

theorem ASRegular.mem_cutEnvelopingAugmentationKernel_iff_operatorSpan
    (hAS : A.ASRegular Q) (x : AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q)) :
    x ∈ hAS.cutEnvelopingAugmentationKernel A Q ↔
      x ∈ Submodule.span k
        ((hAS.periodIso A Q).cutEnvelopingZeroKernelOperators Q ∪
          (hAS.periodIso A Q).cutEnvelopingPositiveHomogeneousOperators Q) := by
  change x ∈ (hAS.periodIso A Q).cutEnvelopingAugmentationKernel Q ↔ _
  rw [← (hAS.periodIso A Q).mem_cutEnvelopingAugmentationKernelSubspace Q,
    (hAS.periodIso A Q).cutEnvelopingAugmentationKernelSubspace_eq_operatorSpan Q]

end ASGinzburg.ZAlgebra
