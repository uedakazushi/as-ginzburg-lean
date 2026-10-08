import ASGinzburg.UnrolledPathKernelSquare
import ASGinzburg.UnrolledPathIdeals

/-! Proposition 1.2's actual kernel-square condition follows from the
original finite minimal AS resolution, with no extra algebraic assumptions. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)
variable (R : ∀ w : Q.LiftVertex, A.ASResolution Q w)

theorem unrolledPathPresentation_kernel_le_arrow_square (i j : ℤ) :
    (A.unrolledPathPresentation Q R).kernel.hom i j ≤
      ((Q.unrolledArrowIdeal k).mul (Q.unrolledArrowIdeal k)).hom i j := by
  rw [Q.unrolledArrowIdeal_square k]
  intro f hf
  apply A.unrolledPathLinearEvaluation_ker_le_long Q R
    (Q.heightEquiv.symm i) (Q.heightEquiv.symm j)
  change A.unrolledPathLinearEvaluation Q R _ _ f = 0
  change A.homTransport _ _ i j (Q.height_heightEquiv_symm i)
    (Q.height_heightEquiv_symm j) (A.unrolledPathLinearEvaluation Q R _ _ f) = 0 at hf
  apply (A.homTransport _ _ i j (Q.height_heightEquiv_symm i)
    (Q.height_heightEquiv_symm j)).injective
  rw [map_zero]
  exact hf

theorem ASRegular.unrolledPathPresentation_kernel_le_arrow_square
    (hAS : A.ASRegular Q) (i j : ℤ) :
    (hAS.unrolledPathPresentation A Q).kernel.hom i j ≤
      ((Q.unrolledArrowIdeal k).mul (Q.unrolledArrowIdeal k)).hom i j :=
  A.unrolledPathPresentation_kernel_le_arrow_square Q (hAS.resolution A Q) i j

/-- A genuine free-path presentation satisfying the kernel condition (1.9).
This is output data, not an additional hypothesis in ASRegular. -/
structure MinimalPathPresentation where
  presentation : Homomorphism (Q.unrolledPathZAlgebra k) A
  surjective : ∀ i j, Function.Surjective (presentation.map i j)
  kernel_square : ∀ i j, presentation.kernel.hom i j ≤
    ((Q.unrolledArrowIdeal k).mul (Q.unrolledArrowIdeal k)).hom i j

noncomputable def ASRegular.minimalPathPresentation (hAS : A.ASRegular Q) :
    A.MinimalPathPresentation Q where
  presentation := hAS.unrolledPathPresentation A Q
  surjective := hAS.unrolledPathPresentation_surjective A Q
  kernel_square := hAS.unrolledPathPresentation_kernel_le_arrow_square A Q

theorem ASRegular.exists_minimalPathPresentation (hAS : A.ASRegular Q) :
    Nonempty (A.MinimalPathPresentation Q) := ⟨hAS.minimalPathPresentation A Q⟩

end ASGinzburg.ZAlgebra
