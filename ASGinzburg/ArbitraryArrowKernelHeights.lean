import ASGinzburg.PeriodicArrowIntegerLinearKernels
import ASGinzburg.ASPathKernelHeights
import ASGinzburg.ArbitraryArrowPresentation

/-! The concrete evaluation kernel of any arrow family is exactly
the kernel of its integer-indexed presentation under the height equivalence. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)
variable (G : A.IncomingElementFamily Q)

theorem unrolledComponentHeightEquiv_mem_arrowPresentation_kernel_iff
    (x y : Q.LiftVertex) (f : Q.UnrolledPathComponent k x y) :
    Q.unrolledComponentHeightEquiv k x y f ∈
        (A.arrowPathPresentation Q G).kernel.hom (Q.height x) (Q.height y) ↔
      A.arrowPathLinearEvaluation Q G x y f = 0 := by
  change A.homTransport _ _ (Q.height x) (Q.height y)
    (Q.height_heightEquiv_symm (Q.height x)) (Q.height_heightEquiv_symm (Q.height y))
      (A.arrowPathLinearEvaluation Q G _ _
        (Finsupp.mapDomain (Q.unrolledPathHeightEquiv x y) f)) = 0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff]
  exact A.arrowPathLinearEvaluation_transport_eq_zero_iff Q G
    (Q.heightEquiv_symm_height x).symm (Q.heightEquiv_symm_height y).symm f

end ASGinzburg.ZAlgebra
