import ASGinzburg.PeriodCutEnvelopingBigrading
import work.ASGinzburgDraft.PeriodCutEnvelopingQuotient

/-! Every positive ordinary enveloping bigrade belongs to the genuine
augmentation kernel. This follows from the actual cut augmentation and
the unsigned tensor map, not from a signed tensor multiplication. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open scoped TensorProduct
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices : ℤ))

theorem cutHomogeneousInclusion_mem_gradedJacobson_of_ne_zero
    (m : ℕ) (hm : m ≠ 0)
    (x : E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) m) :
    E.cutHomogeneousInclusion (fun i : Q.Vertex => (i.val : ℤ)) m x ∈
      E.cutGradedJacobson Q := by
  rw [E.cutGradedJacobson_eq_augmentationKernel Q]
  change E.cutAugmentation Q
    (E.cutHomogeneousInclusion (fun i : Q.Vertex => (i.val : ℤ)) m x) = 0
  rw [E.cutAugmentation_homogeneous Q]
  exact E.cutAugmentationComponent_ne_zero Q hm x

set_option synthInstance.maxHeartbeats 200000 in
theorem cutEnvelopingAugmentation_homogeneous_ne_zero
    (d : ℕ × ℕ) (hd : d.1 + d.2 ≠ 0)
    (x : E.CutEnvelopingBlock (fun i : Q.Vertex => (i.val : ℤ)) d) :
    E.cutEnvelopingAugmentation Q
      (E.cutEnvelopingHomogeneousInclusion (fun i : Q.Vertex => (i.val : ℤ)) d x) = 0 := by
  rcases d with ⟨i, j⟩
  induction x using TensorProduct.induction_on with
  | zero =>
      rw [(E.cutEnvelopingHomogeneousInclusion
        (fun i : Q.Vertex => (i.val : ℤ)) (i, j)).map_zero]
      exact (E.cutEnvelopingAugmentation Q).map_zero
  | tmul x y =>
      rw [E.cutEnvelopingHomogeneousInclusion_tmul]
      unfold cutEnvelopingAugmentation
      rw [algebraEnvelopingQuotientAugmentation_tmul]
      by_cases hi : i = 0
      · have hj : j ≠ 0 := by simpa [hi] using hd
        rw [(Ideal.Quotient.eq_zero_iff_mem).mpr
          (E.cutHomogeneousInclusion_mem_gradedJacobson_of_ne_zero Q j hj y),
          MulOpposite.op_zero, TensorProduct.tmul_zero]
      · rw [(Ideal.Quotient.eq_zero_iff_mem).mpr
          (E.cutHomogeneousInclusion_mem_gradedJacobson_of_ne_zero Q i hi x),
          TensorProduct.zero_tmul]
  | add x y hx hy =>
      calc
        _ = E.cutEnvelopingAugmentation Q
            (E.cutEnvelopingHomogeneousInclusion (fun i : Q.Vertex => (i.val : ℤ))
              (i, j) x) + E.cutEnvelopingAugmentation Q
            (E.cutEnvelopingHomogeneousInclusion (fun i : Q.Vertex => (i.val : ℤ))
              (i, j) y) :=
          ((E.cutEnvelopingAugmentation Q).toLinearMap.comp
            (E.cutEnvelopingHomogeneousInclusion
              (fun i : Q.Vertex => (i.val : ℤ)) (i, j))).map_add x y
        _ = 0 := by rw [hx, hy, add_zero]

theorem cutEnvelopingHomogeneousInclusion_mem_augmentationKernel
    (d : ℕ × ℕ) (hd : d.1 + d.2 ≠ 0)
    (x : E.CutEnvelopingBlock (fun i : Q.Vertex => (i.val : ℤ)) d) :
    E.cutEnvelopingHomogeneousInclusion (fun i : Q.Vertex => (i.val : ℤ)) d x ∈
      E.cutEnvelopingAugmentationKernel Q :=
  (E.mem_cutEnvelopingAugmentationKernel Q _).mpr
    (E.cutEnvelopingAugmentation_homogeneous_ne_zero Q d hd x)

end ASGinzburg.ZAlgebra.PeriodIso
