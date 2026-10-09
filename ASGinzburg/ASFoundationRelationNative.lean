import ASGinzburg.ASRegularRelationRepresentatives
import ASGinzburg.ASRelationKernelHeightEquiv

/-! The actual chosen minimal relation representatives, before erasing
sheets, are genuine lifted paths in the kernel of AS evaluation. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

set_option synthInstance.maxHeartbeats 200000 in
noncomputable def ASRegular.foundationRelationNative (hAS : A.ASRegular Q)
    (i j : Q.Vertex) (a : Q.FoundationRelationArrow i j) :
    LinearMap.ker (A.unrolledPathLinearEvaluation Q (hAS.resolution A Q) (i,0) (j,0)) :=
  (A.pathRelationHeightEquiv Q (hAS.resolution A Q) (i,0) (j,0)).symm
    (by simpa only [CutQuiver.height,mul_zero,add_zero] using hAS.foundationRelationLift A Q i j a)

set_option synthInstance.maxHeartbeats 200000 in
theorem ASRegular.foundationRelationNative_height (hAS : A.ASRegular Q)
    (i j : Q.Vertex) (a : Q.FoundationRelationArrow i j) :
    Q.unrolledComponentHeightEquiv k (i,0) (j,0)
      (hAS.foundationRelationNative A Q i j a).val=
        (hAS.foundationRelationLift A Q i j a).val := by
  let f : (A.unrolledPathPresentation Q (hAS.resolution A Q)).kernel.hom
      (Q.height (i,0)) (Q.height (j,0)) :=
    by simpa only [CutQuiver.height,mul_zero,add_zero] using hAS.foundationRelationLift A Q i j a
  exact congrArg Subtype.val
    ((A.pathRelationHeightEquiv Q (hAS.resolution A Q) (i,0) (j,0)).apply_symm_apply f)

set_option synthInstance.maxHeartbeats 200000 in
theorem ASRegular.foundationRelationNative_mem_long (hAS : A.ASRegular Q)
    (i j : Q.Vertex) (a : Q.FoundationRelationArrow i j) :
    (hAS.foundationRelationNative A Q i j a).val ∈
      Q.unrolledPathFiltration k 2 (i,0) (j,0) :=
  A.unrolledPathLinearEvaluation_ker_le_long Q (hAS.resolution A Q) (i,0) (j,0)
    (hAS.foundationRelationNative A Q i j a).property

end ASGinzburg.ZAlgebra
