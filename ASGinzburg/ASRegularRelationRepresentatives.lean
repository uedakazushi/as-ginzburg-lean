import ASGinzburg.ASRegularMinimalRelationBasis
import ASGinzburg.MinimalRelationBasisLifts

/-! Actual cut-indexed relation representatives exist under the
original ASRegular conditions, and generate the genuine relation
component modulo IJ+JI. Foundation descent remains a further proof. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

set_option synthInstance.maxHeartbeats 200000 in
noncomputable def ASRegular.foundationRelationLift (hAS : A.ASRegular Q)
    (i j : Q.Vertex) (a : Q.FoundationRelationArrow i j) :
    (hAS.unrolledPathPresentation A Q).kernel.hom (i.val : ℤ) (j.val : ℤ) :=
  Q.minimalRelationBasisLift (hAS.unrolledPathPresentation A Q).kernel
    (i.val : ℤ) (j.val : ℤ) (hAS.foundationMinimalRelationBasis A Q i j) a

set_option synthInstance.maxHeartbeats 200000 in
theorem ASRegular.foundationRelationLift_class (hAS : A.ASRegular Q)
    (i j : Q.Vertex) (a : Q.FoundationRelationArrow i j) :
    (Submodule.Quotient.mk (hAS.foundationRelationLift A Q i j a) :
      Q.MinimalRelationComponent (hAS.unrolledPathPresentation A Q).kernel
        (i.val : ℤ) (j.val : ℤ))=hAS.foundationMinimalRelationBasis A Q i j a :=
  Q.minimalRelationBasisLift_class (hAS.unrolledPathPresentation A Q).kernel
    (i.val : ℤ) (j.val : ℤ) (hAS.foundationMinimalRelationBasis A Q i j) a

set_option synthInstance.maxHeartbeats 200000 in
theorem ASRegular.foundationRelationLift_ambient_decomposition (hAS : A.ASRegular Q)
    (i j : Q.Vertex) :
    Submodule.span k (Set.range (fun a => (hAS.foundationRelationLift A Q i j a).val)) ⊔
      Q.relationDecomposables (hAS.unrolledPathPresentation A Q).kernel
        (i.val : ℤ) (j.val : ℤ)=
      (hAS.unrolledPathPresentation A Q).kernel.hom (i.val : ℤ) (j.val : ℤ) :=
  Q.minimalRelationBasisLift_ambient_decomposition (hAS.unrolledPathPresentation A Q).kernel
    (i.val : ℤ) (j.val : ℤ) (hAS.foundationMinimalRelationBasis A Q i j)

end ASGinzburg.ZAlgebra
