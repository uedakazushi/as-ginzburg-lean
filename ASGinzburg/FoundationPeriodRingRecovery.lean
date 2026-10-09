import ASGinzburg.FoundationPeriodZeroKernel
import ASGinzburg.ASFoundationJacobianRingEquiv

/-! The foundation restriction of the actual period-transported
presentation has precisely the candidate's cut Jacobian kernel and
recovers the original foundation ring. The full Jacobian comparison
and Ginzburg regularity are still separate proof obligations. -/
namespace ASGinzburg.ZAlgebra
universe u
variable {k : Type u} [Field k] (A : ZAlgebra.{u,u} k) (Q : CutQuiver)

noncomputable def ASRegular.foundationPeriodRingPresentation (hAS : A.ASRegular Q) :
    (Q.unrolledPathZAlgebra k).FoundationAlgebra Q →ₐ[k] A.FoundationAlgebra Q :=
  (A.arrowPathPresentation Q (hAS.foundationPeriodIncomingElement A Q)).foundationAlgebraMap Q

theorem ASRegular.foundationPeriodRingPresentation_eq (hAS : A.ASRegular Q) :
    hAS.foundationPeriodRingPresentation A Q=hAS.foundationRingPresentation A Q := by
  apply AlgHom.ext
  intro x
  funext i j
  exact congrArg (fun f => f (x i j)) (hAS.foundationPeriodPathPresentation_zeroSheet A Q i j)

theorem ASRegular.foundationPeriodRingPresentation_surjective (hAS : A.ASRegular Q) :
    Function.Surjective (hAS.foundationPeriodRingPresentation A Q) :=
  (A.arrowPathPresentation Q (hAS.foundationPeriodIncomingElement A Q)).foundationAlgebraMap_surjective
    Q (hAS.foundationPeriodPathPresentation_surjective A Q)

noncomputable def ASRegular.foundationPeriodZeroCutPresentation (hAS : A.ASRegular Q) :
    Q.ZeroCutPathRing k →ₐ[k] A.FoundationAlgebra Q :=
  (hAS.foundationPeriodRingPresentation A Q).comp (Q.zeroCutFoundationRingAlgEquiv k).toAlgHom

theorem ASRegular.foundationPeriodZeroCutPresentation_eq (hAS : A.ASRegular Q) :
    hAS.foundationPeriodZeroCutPresentation A Q=hAS.foundationZeroCutPresentation A Q := by
  rw [foundationPeriodZeroCutPresentation,hAS.foundationPeriodRingPresentation_eq A Q]
  rfl

theorem ASRegular.foundationPeriodZeroCutPresentation_surjective (hAS : A.ASRegular Q) :
    Function.Surjective (hAS.foundationPeriodZeroCutPresentation A Q) :=
  (hAS.foundationPeriodRingPresentation_surjective A Q).comp (Q.zeroCutFoundationRingAlgEquiv k).surjective

theorem ASRegular.foundationPeriodZeroCutKernel_eq_Jacobian (hAS : A.ASRegular Q) :
    RingHom.ker (hAS.foundationPeriodZeroCutPresentation A Q).toRingHom=
      Q.zeroCutJacobianIdeal k (hAS.foundationPotential A Q) := by
  rw [hAS.foundationPeriodZeroCutPresentation_eq A Q]
  exact (hAS.foundationZeroCutRelationIdeal_eq_kernel A Q).symm.trans
    (hAS.foundationPotential_zeroCutJacobianIdeal A Q)

noncomputable def ASRegular.foundationPeriodJacobianRingAlgEquiv (hAS : A.ASRegular Q) :
    Q.ZeroCutJacobianRing k (hAS.foundationPotential A Q) ≃ₐ[k] A.FoundationAlgebra Q :=
  (Ideal.quotientEquivAlgOfEq k (hAS.foundationPeriodZeroCutKernel_eq_Jacobian A Q).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (hAS.foundationPeriodZeroCutPresentation_surjective A Q))

end ASGinzburg.ZAlgebra
