import ASGinzburg.GinzburgIndexedArrowReflection
import ASGinzburg.GinzburgOppositeHessianProducts

/-! Reflection preserves the actual endpoint-arrow matrix products
needed by the first and third canonical A-dual differentials. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k] (φ : Q.Potential k)

theorem ginzburgOppositeOriginalArrowProduct (v l : Q.LiftVertex)
    (a : Q.GinzburgIncomingDegree v.1 0)
    (f : (Q.unrolledJacobianZAlgebra k φ).Hom (Q.height v) (Q.height l)) :
    (Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).homTransport
      _ _ _ _ rfl
      (congrArg Q.opposite.height (Q.ginzburgOriginalOppositeDualEndpoint v a).symm)
      (Q.oppositeUnrolledJacobianHomEquiv k φ (Q.ginzburgPrefixGeneratorEndpoint v a.val) l
        ((Q.unrolledJacobianZAlgebra k φ).comp f (Q.ginzburgGeneratorOriginalArrowEntry k φ v a)))=
      (Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).comp
        (Q.opposite.ginzburgGeneratorLoopArrowEntry k (Q.oppositePotentialEquiv k φ)
          (Q.ginzburgDualOppositeBase v) (Q.ginzburgOriginalOppositeDualEquiv v a))
        ((Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).homTransport
          _ _ _ _ rfl
          (congrArg Q.opposite.height (Q.ginzburgDualOppositeBase_previous v).symm)
          (Q.oppositeUnrolledJacobianHomEquiv k φ v l f)) := by
  rw [Q.oppositeUnrolledJacobianHomEquiv_comp]
  rw [(Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).homTransport_comp
    _ _ _ _
    (Q.opposite.height (Q.opposite.tau.symm (Q.ginzburgDualOppositeBase v))) _ rfl
    (congrArg Q.opposite.height (Q.ginzburgDualOppositeBase_previous v).symm)
    (congrArg Q.opposite.height (Q.ginzburgOriginalOppositeDualEndpoint v a).symm)]
  rw [Q.ginzburgGeneratorOriginalArrowEntry_opposite_indexed]
  rfl

theorem ginzburgOppositeLoopArrowProduct (v l : Q.LiftVertex)
    (a : Q.GinzburgIncomingDegree v.1 (-1))
    (f : (Q.unrolledJacobianZAlgebra k φ).Hom
      (Q.height (Q.ginzburgPrefixGeneratorEndpoint v a.val)) (Q.height l)) :
    Q.oppositeUnrolledJacobianHomEquiv k φ (Q.tau.symm v) l
      ((Q.unrolledJacobianZAlgebra k φ).comp f (Q.ginzburgGeneratorLoopArrowEntry k φ v a))=
      (Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).comp
        (Q.opposite.ginzburgGeneratorOriginalArrowEntry k (Q.oppositePotentialEquiv k φ)
          (Q.ginzburgDualOppositeBase v) (Q.ginzburgDualOppositeOriginalEquiv v a))
        ((Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).homTransport
          _ _ _ _ rfl
          (congrArg Q.opposite.height (Q.ginzburgDualOppositeOriginalEndpoint v a).symm)
          (Q.oppositeUnrolledJacobianHomEquiv k φ
            (Q.ginzburgPrefixGeneratorEndpoint v a.val) l f)) := by
  change (Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).homTransport
    _ _ _ _ rfl rfl
    (Q.oppositeUnrolledJacobianHomEquiv k φ (Q.tau.symm v) l
      ((Q.unrolledJacobianZAlgebra k φ).comp f (Q.ginzburgGeneratorLoopArrowEntry k φ v a)))=_
  rw [Q.oppositeUnrolledJacobianHomEquiv_comp]
  rw [(Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).homTransport_comp
    _ _ _ _
    (Q.opposite.height (Q.opposite.ginzburgPrefixGeneratorEndpoint
      (Q.ginzburgDualOppositeBase v) (Q.ginzburgDualOppositeOriginalEquiv v a).val)) _ rfl
    (congrArg Q.opposite.height (Q.ginzburgDualOppositeOriginalEndpoint v a).symm) rfl]
  rw [Q.ginzburgGeneratorLoopArrowEntry_opposite_indexed]
  rfl

end ASGinzburg.CutQuiver
