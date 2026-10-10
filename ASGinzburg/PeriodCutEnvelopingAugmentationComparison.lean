import ASGinzburg.PeriodCutEnvelopingQuotient
import ASGinzburg.AlgebraEnvelopingMap
import ASGinzburg.PeriodCutZeroScalarCharacters

/-! Compare the genuine quotient enveloping augmentation with the tensor
of the original cut augmentation. On the actual degree-zero subalgebra
this is precisely the tensor of the genuine scalar-diagonal map. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open scoped TensorProduct
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices : ℤ))

theorem cutGradedSemisimpleQuotientAlgEquiv_mk
    (x : E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ))) :
    E.cutGradedSemisimpleQuotientAlgEquiv Q
      (Ideal.Quotient.mk (E.cutGradedJacobson Q) x) = E.cutAugmentation Q x := by
  rw [cutGradedSemisimpleQuotientAlgEquiv, AlgEquiv.trans_apply,
    Ideal.quotientEquivAlgOfEq_mk]
  rfl

noncomputable def cutEnvelopingQuotientTensorEquiv :
    AlgebraEnvelopingRing k
      (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)) ⧸ E.cutGradedJacobson Q) ≃ₐ[k]
        AlgebraEnvelopingRing k (Q.Vertex → k) :=
  Algebra.TensorProduct.congr (E.cutGradedSemisimpleQuotientAlgEquiv Q)
    (E.cutGradedSemisimpleQuotientAlgEquiv Q).op

set_option synthInstance.maxHeartbeats 200000 in
theorem cutEnvelopingAugmentation_tensorComparison
    (x : AlgebraEnvelopingRing k
      (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))) :
    E.cutEnvelopingQuotientTensorEquiv Q (E.cutEnvelopingAugmentation Q x) =
      algebraEnvelopingMap k (E.cutAugmentation Q) x := by
  let f := (E.cutEnvelopingQuotientTensorEquiv Q).toLinearMap.comp
    (E.cutEnvelopingAugmentation Q).toLinearMap
  let g := (algebraEnvelopingMap k (E.cutAugmentation Q)).toLinearMap
  change f x = g x
  induction x using TensorProduct.induction_on with
  | zero => exact f.map_zero.trans g.map_zero.symm
  | tmul a b =>
      obtain ⟨b, rfl⟩ := MulOpposite.op_surjective b
      change E.cutGradedSemisimpleQuotientAlgEquiv Q
          (Ideal.Quotient.mk (E.cutGradedJacobson Q) a) ⊗ₜ[k]
          MulOpposite.op (E.cutGradedSemisimpleQuotientAlgEquiv Q
            (Ideal.Quotient.mk (E.cutGradedJacobson Q) b)) =
        E.cutAugmentation Q a ⊗ₜ[k] MulOpposite.op (E.cutAugmentation Q b)
      rw [E.cutGradedSemisimpleQuotientAlgEquiv_mk Q,
        E.cutGradedSemisimpleQuotientAlgEquiv_mk Q]
  | add x y hx hy =>
      exact (f.map_add x y).trans
        ((congrArg₂ (· + ·) hx hy).trans (g.map_add x y).symm)

set_option synthInstance.maxHeartbeats 200000 in
theorem cutEnvelopingAugmentationKernel_eq_scalarKernel :
    E.cutEnvelopingAugmentationKernel Q =
      algebraEnvelopingMapKernel k (E.cutAugmentation Q) := by
  ext x
  rw [E.mem_cutEnvelopingAugmentationKernel Q, mem_algebraEnvelopingMapKernel]
  constructor
  · intro hx
    rw [← E.cutEnvelopingAugmentation_tensorComparison Q x, hx]
    exact (E.cutEnvelopingQuotientTensorEquiv Q).map_zero
  · intro hx
    apply (E.cutEnvelopingQuotientTensorEquiv Q).injective
    exact (E.cutEnvelopingAugmentation_tensorComparison Q x).trans
      (hx.trans (E.cutEnvelopingQuotientTensorEquiv Q).map_zero.symm)

theorem cutAugmentation_comp_cutZeroRingInclusion :
    (E.cutAugmentation Q).comp (E.cutZeroRingInclusion Q) = E.cutZeroDiagonalAlgHom Q := by
  apply AlgHom.ext
  intro x
  exact E.cutAugmentation_zero_component Q x

noncomputable def cutEnvelopingZeroInclusion :
    AlgebraEnvelopingRing k
      (E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) 0) →ₐ[k]
        AlgebraEnvelopingRing k (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ))) :=
  algebraEnvelopingMap k (E.cutZeroRingInclusion Q)

theorem cutEnvelopingZeroInclusion_tmul
    (a b : E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) 0) :
    E.cutEnvelopingZeroInclusion Q (a ⊗ₜ[k] MulOpposite.op b) =
      E.cutHomogeneousInclusion (fun i : Q.Vertex => (i.val : ℤ)) 0 a ⊗ₜ[k]
        MulOpposite.op
          (E.cutHomogeneousInclusion (fun i : Q.Vertex => (i.val : ℤ)) 0 b) := rfl

theorem cutEnvelopingVertexAugmentation_comp_zeroInclusion :
    (algebraEnvelopingMap k (E.cutAugmentation Q)).comp
      (E.cutEnvelopingZeroInclusion Q) =
        algebraEnvelopingMap k (E.cutZeroDiagonalAlgHom Q) := by
  unfold cutEnvelopingZeroInclusion algebraEnvelopingMap
  rw [← Algebra.TensorProduct.map_comp]
  change Algebra.TensorProduct.map
      ((E.cutAugmentation Q).comp (E.cutZeroRingInclusion Q))
      ((E.cutAugmentation Q).comp (E.cutZeroRingInclusion Q)).op = _
  rw [E.cutAugmentation_comp_cutZeroRingInclusion Q]

set_option synthInstance.maxHeartbeats 200000 in
theorem cutEnvelopingAugmentationKernel_comap_zeroInclusion :
    (E.cutEnvelopingAugmentationKernel Q).comap (E.cutEnvelopingZeroInclusion Q) =
      algebraEnvelopingMapKernel k (E.cutZeroDiagonalAlgHom Q) := by
  rw [E.cutEnvelopingAugmentationKernel_eq_scalarKernel Q]
  ext x
  rw [Ideal.mem_comap, mem_algebraEnvelopingMapKernel, mem_algebraEnvelopingMapKernel]
  change ((algebraEnvelopingMap k (E.cutAugmentation Q)).comp
    (E.cutEnvelopingZeroInclusion Q)) x = 0 ↔ _
  rw [E.cutEnvelopingVertexAugmentation_comp_zeroInclusion Q]

end ASGinzburg.ZAlgebra.PeriodIso
