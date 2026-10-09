import ASGinzburg.FoundationPeriodJacobianCutKernel
import ASGinzburg.UnrolledCutJacobianIdeal

/-! Without additional relation hypotheses, the original AS condition
annihilates the two-sided ideal of all sheet lifts of cut derivatives. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem ASRegular.foundationPeriodCutJacobianGenerators_mem_kernel
    (hAS : A.ASRegular Q) (i j : ℤ) :
    Q.cutJacobianGenerators k (hAS.foundationPotential A Q) i j ⊆
      (A.arrowPathPresentation Q (hAS.foundationPeriodIncomingElement A Q)).kernel.hom i j := by
  rintro f ⟨a,m,ha,hi,hj,rfl⟩
  subst i
  subst j
  exact hAS.foundationPeriodIntegerJacobianRelation_cut_mem_kernel A Q a ha m

theorem ASRegular.foundationPeriodCutJacobianIdeal_le_kernel
    (hAS : A.ASRegular Q) (i j : ℤ) :
    (Q.unrolledCutJacobianIdeal k (hAS.foundationPotential A Q)).hom i j ≤
      (A.arrowPathPresentation Q (hAS.foundationPeriodIncomingElement A Q)).kernel.hom i j :=
  LinearIdeal.generated_le _ _ (hAS.foundationPeriodCutJacobianGenerators_mem_kernel A Q) i j

end ASGinzburg.ZAlgebra
