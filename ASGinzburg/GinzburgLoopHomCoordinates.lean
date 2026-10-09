import ASGinzburg.FiniteRepresentableHomCoordinates
import ASGinzburg.GinzburgGeneratorLoopProjective
import ASGinzburg.GinzburgOppositeDualIndices
import ASGinzburg.OppositeUnrolledJacobianHom

/-! The genuine loop coproduct has one actual coordinate. Its Hom space
and evaluation components give the two endpoint comparison isomorphisms. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def ginzburgLoopCoefficientEvaluationEquiv (w : Q.LiftVertex) (l : ℤ) :
    (A.rightModuleEvaluation l).obj (A.ginzburgGeneratorCoefficientModule Q w (-2)) ≃ₗ[k]
      A.Hom l (Q.height (Q.tau.symm w)) :=
  (A.ginzburgGeneratorCoefficientComponentEquiv Q w (-2) l).trans
    (((LinearEquiv.piCongrLeft k (fun a : Q.GinzburgIncomingDegree w.1 (-2) =>
      A.Hom l (Q.height (Q.ginzburgPrefixGeneratorEndpoint w a.val)))
      (Q.ginzburgLoopGeneratorEquiv w)).symm).trans
      (LinearEquiv.funUnique PUnit.{1} k (A.Hom l (Q.height (Q.tau.symm w)))))

noncomputable def ginzburgLoopRepresentableHomEquiv (w : Q.LiftVertex) (l : ℤ) :
    (A.ginzburgGeneratorCoefficientModule Q w (-2) ⟶ A.representable l) ≃ₗ[k]
      A.Hom (Q.height (Q.tau.symm w)) l :=
  (A.rightRepresentableCoproductHomEquiv
    (fun a : Q.GinzburgIncomingDegree w.1 (-2) =>
      Q.height (Q.ginzburgPrefixGeneratorEndpoint w a.val)) (A.representable l)).trans
    (((LinearEquiv.piCongrLeft k (fun a : Q.GinzburgIncomingDegree w.1 (-2) =>
      A.Hom (Q.height (Q.ginzburgPrefixGeneratorEndpoint w a.val)) l)
      (Q.ginzburgLoopGeneratorEquiv w)).symm).trans
      (LinearEquiv.funUnique PUnit.{1} k (A.Hom (Q.height (Q.tau.symm w)) l)))

theorem ginzburgLoopCoefficientEvaluationEquiv_apply (w : Q.LiftVertex) (l : ℤ)
    (x : (A.rightModuleEvaluation l).obj (A.ginzburgGeneratorCoefficientModule Q w (-2))) :
    A.ginzburgLoopCoefficientEvaluationEquiv Q w l x=
      A.ginzburgGeneratorCoefficientComponentEquiv Q w (-2) l x ⟨.loop w.1,rfl,rfl⟩ := rfl

theorem ginzburgLoopRepresentableHomEquiv_apply (w : Q.LiftVertex) (l : ℤ)
    (f : A.ginzburgGeneratorCoefficientModule Q w (-2) ⟶ A.representable l) :
    A.ginzburgLoopRepresentableHomEquiv Q w l f=
      A.rightRepresentableCoproductHomEquiv
        (fun a : Q.GinzburgIncomingDegree w.1 (-2) =>
          Q.height (Q.ginzburgPrefixGeneratorEndpoint w a.val)) (A.representable l) f
          ⟨.loop w.1,rfl,rfl⟩ := rfl

end ASGinzburg.ZAlgebra

namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k] (φ : Q.Potential k)

theorem ginzburgDualOppositeBase_previous (v : Q.LiftVertex) :
    Q.opposite.tau.symm (Q.ginzburgDualOppositeBase v)=Q.oppositeLiftVertexEquiv v := by
  apply Prod.ext
  · rfl
  · change -(v.2-1)-1= -v.2
    omega

noncomputable def ginzburgRepresentableADualOppositeLoopComponentEquiv (v l : Q.LiftVertex) :
    ((Q.unrolledJacobianZAlgebra k φ).representable (Q.height v) ⟶
      (Q.unrolledJacobianZAlgebra k φ).representable (Q.height l)) ≃ₗ[k]
    ((Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).rightModuleEvaluation
      (Q.opposite.height (Q.oppositeLiftVertexEquiv l))).obj
      ((Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).ginzburgGeneratorCoefficientModule Q.opposite (Q.ginzburgDualOppositeBase v) (-2)) :=
  ((Q.unrolledJacobianZAlgebra k φ).representableYonedaEquiv (Q.height v)
    ((Q.unrolledJacobianZAlgebra k φ).representable (Q.height l))).trans
    ((Q.oppositeUnrolledJacobianHomEquiv k φ v l).trans
      (((Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).homTransport
        _ _ _ _ rfl (congrArg Q.opposite.height (Q.ginzburgDualOppositeBase_previous v).symm)).trans
        ((Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).ginzburgLoopCoefficientEvaluationEquiv Q.opposite (Q.ginzburgDualOppositeBase v)
            (Q.opposite.height (Q.oppositeLiftVertexEquiv l))).symm))

noncomputable def ginzburgLoopADualOppositeRepresentableComponentEquiv (v l : Q.LiftVertex) :
    ((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientModule Q v (-2) ⟶
      (Q.unrolledJacobianZAlgebra k φ).representable (Q.height l)) ≃ₗ[k]
    (Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).Hom
      (Q.opposite.height (Q.oppositeLiftVertexEquiv l))
      (Q.opposite.height (Q.ginzburgDualOppositeBase v)) :=
  ((Q.unrolledJacobianZAlgebra k φ).ginzburgLoopRepresentableHomEquiv Q v (Q.height l)).trans
    (Q.oppositeUnrolledJacobianHomEquiv k φ (Q.tau.symm v) l)

end ASGinzburg.CutQuiver
