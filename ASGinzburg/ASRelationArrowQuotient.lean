import ASGinzburg.ASRelationKernelHeightEquiv
import ASGinzburg.ASFirstKernelComponentComparison

/-! The original presentation kernel modulo its genuine right arrow
product is the actual categorical first AS kernel, in every off-diagonal
lifted component. Radical/top compatibility remains a further theorem. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)
  (R : ∀ w : Q.LiftVertex, A.ASResolution Q w)

noncomputable def presentationRelationArrowQuotientFirstKernelEquiv
    (u w : Q.LiftVertex) (huw : u≠w) :
    ((A.unrolledPathPresentation Q R).kernel.hom (Q.height u) (Q.height w) ⧸
      Submodule.comap ((A.unrolledPathPresentation Q R).kernel.hom
        (Q.height u) (Q.height w)).subtype
        (((A.unrolledPathPresentation Q R).kernel.mul (Q.unrolledArrowIdeal k)).hom
          (Q.height u) (Q.height w))) ≃ₗ[k]
      (A.rightModuleEvaluation (Q.height u)).obj (kernel (R w).d₁) :=
  ((Submodule.Quotient.equiv _ _ (A.pathRelationHeightEquiv Q R u w)
    (A.pathRelationHeightEquiv_map_firstKernel_denominator Q R u w huw)).symm.trans
      (A.pathRelationsFirstKernelEquiv Q R u w huw)).trans
        (A.asFirstKernelComponentEquiv Q R u w).symm

end ASGinzburg.ZAlgebra
