import ASGinzburg.ZeroCutFoundationRingEquiv
import ASGinzburg.UnrolledJacobianAlgebra
import ASGinzburg.UnrolledJacobianLiftIdeal
import ASGinzburg.PathJacobianLengthSupport

/-! The native noncut free-path components surject onto the original
Jacobian foundation. Their genuine kernels have no constant or arrow terms. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def zeroCutJacobianComponentProjection (φ : Q.Potential k) (i j : Q.Vertex) :
    Q.pathCutComponent k i j 0 →ₗ[k]
      (Q.unrolledJacobianZAlgebra k φ).Hom (i.val : ℤ) (j.val : ℤ) :=
  ((Q.unrolledJacobianQuotientMap k φ).map (i.val : ℤ) (j.val : ℤ)).comp
    (Q.zeroCutFoundationComponentEquiv k i j).toLinearMap

theorem zeroCutJacobianComponentProjection_surjective (φ : Q.Potential k) (i j : Q.Vertex) :
    Function.Surjective (Q.zeroCutJacobianComponentProjection k φ i j) :=
  (Q.unrolledJacobianQuotientMap_surjective k φ _ _).comp
    (Q.zeroCutFoundationComponentEquiv k i j).surjective

theorem zeroCutJacobianComponentProjection_id (φ : Q.Potential k) (i : Q.Vertex) :
    Q.zeroCutJacobianComponentProjection k φ i i (Q.zeroCutPathId k i) =
      (Q.unrolledJacobianZAlgebra k φ).id (i.val : ℤ) := by
  change (Q.unrolledJacobianQuotientMap k φ).map _ _
    (Q.zeroCutFoundationComponentEquiv k i i (Q.zeroCutPathId k i)) = _
  rw [Q.zeroCutFoundationComponentEquiv_id]
  exact (Q.unrolledJacobianQuotientMap k φ).map_id _

theorem zeroCutJacobianComponentProjection_comp (φ : Q.Potential k) {i j l : Q.Vertex}
    (f : Q.pathCutComponent k i j 0) (g : Q.pathCutComponent k j l 0) :
    Q.zeroCutJacobianComponentProjection k φ i l (Q.zeroCutPathComp k g f) =
      (Q.unrolledJacobianZAlgebra k φ).comp
        (Q.zeroCutJacobianComponentProjection k φ j l g)
        (Q.zeroCutJacobianComponentProjection k φ i j f) := by
  change (Q.unrolledJacobianQuotientMap k φ).map _ _
    (Q.zeroCutFoundationComponentEquiv k i l (Q.zeroCutPathComp k g f)) = _
  rw [Q.zeroCutFoundationComponentEquiv_comp]
  exact (Q.unrolledJacobianQuotientMap k φ).map_comp _ _

theorem zeroCutFoundationComponentEquiv_native (i j : Q.Vertex)
    (f : Q.pathCutComponent k i j 0) :
    Q.zeroCutFoundationComponentEquiv k i j f =
      (show (Q.unrolledPathZAlgebra k).Hom (i.val : ℤ) (j.val : ℤ) from
        Q.unrolledComponentHeightEquiv k (i,0) (j,0)
          (Q.zeroCutNativeUnrollingEquiv k i j f)) := by
  rfl

theorem zeroCutJacobianComponentProjection_eq_zero_iff (φ : Q.Potential k) (i j : Q.Vertex)
    (f : Q.pathCutComponent k i j 0) :
    Q.zeroCutJacobianComponentProjection k φ i j f = 0 ↔
      f.val ∈ (Q.pathJacobianIdeal k φ).hom i j := by
  change (Submodule.Quotient.mk
    (Q.zeroCutFoundationComponentEquiv k i j f) = 0) ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  rw [Q.zeroCutFoundationComponentEquiv_native]
  change Q.zeroCutNativeUnrollingEquiv k i j f ∈
    Q.unrolledJacobianLiftIdeal k φ (i,0) (j,0) ↔ _
  rw [Q.unrolledJacobianLiftIdeal_mem_iff_erase,
    Q.zeroCutNativeUnrollingEquiv_erase]

theorem zeroCutJacobianComponentProjection_kernel_length (φ : Q.Potential k) (i j : Q.Vertex)
    (f : Q.pathCutComponent k i j 0)
    (hf : Q.zeroCutJacobianComponentProjection k φ i j f = 0) :
    f.val ∈ Q.pathLengthFiltration k 2 i j :=
  Q.pathJacobianIdeal_le_lengthFiltration k φ i j
    ((Q.zeroCutJacobianComponentProjection_eq_zero_iff k φ i j f).mp hf)

end ASGinzburg.CutQuiver
