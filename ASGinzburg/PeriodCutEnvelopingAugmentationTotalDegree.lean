import ASGinzburg.PeriodCutEnvelopingDegreeInclusion
import ASGinzburg.PeriodCutEnvelopingAugmentationBigrading

/-! The genuine enveloping augmentation kills every positive total-degree
homogeneous component. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open scoped TensorProduct DirectSum
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices : ℤ))

set_option synthInstance.maxHeartbeats 200000 in
theorem cutEnvelopingAugmentation_degreeInclusion_pos (n : ℕ) (hn : 0 < n)
    (x : E.CutEnvelopingDegreeBlock (fun i : Q.Vertex => (i.val : ℤ)) n) :
    E.cutEnvelopingAugmentation Q
      (E.cutEnvelopingDegreeInclusion (fun i : Q.Vertex => (i.val : ℤ)) n x) = 0 := by
  let f := (E.cutEnvelopingAugmentation Q).toLinearMap.comp
    (E.cutEnvelopingDegreeInclusion (fun i : Q.Vertex => (i.val : ℤ)) n)
  change f x = 0
  induction x using DirectSum.induction_on with
  | zero => exact f.map_zero
  | of d b =>
      change E.cutEnvelopingAugmentation Q
        (E.cutEnvelopingDegreeInclusion (fun i : Q.Vertex => (i.val : ℤ)) n
          (DirectSum.lof k (CutEnvelopingDegreePairs n)
            (fun d => E.CutEnvelopingBlock (fun i : Q.Vertex => (i.val : ℤ)) d.val) d b)) = 0
      rw [E.cutEnvelopingDegreeInclusion_lof]
      exact E.cutEnvelopingAugmentation_homogeneous_ne_zero Q d.val
        (by rw [d.property]; exact Nat.ne_of_gt hn) b
  | add x y hx hy =>
      exact (f.map_add x y).trans ((congrArg₂ (· + ·) hx hy).trans (add_zero 0))

theorem cutEnvelopingHomogeneousSubspace_le_augmentationKernel (n : ℕ) (hn : 0 < n)
    {x : AlgebraEnvelopingRing k (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))}
    (hx : x ∈ E.cutEnvelopingHomogeneousSubspace (fun i : Q.Vertex => (i.val : ℤ)) n) :
    x ∈ E.cutEnvelopingAugmentationKernel Q := by
  obtain ⟨b,rfl⟩ := hx
  exact (E.mem_cutEnvelopingAugmentationKernel Q _).mpr
    (E.cutEnvelopingAugmentation_degreeInclusion_pos Q n hn b)

end ASGinzburg.ZAlgebra.PeriodIso
