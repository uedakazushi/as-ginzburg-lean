import ASGinzburg.OppositeReflectedJacobianIso
import ASGinzburg.ReflectedLinearCategory
import ASGinzburg.ZAlgebraLinearEquivalence
import ASGinzburg.LinearRepresentationEquivalence
import ASGinzburg.LeftModuleAbelian

/-! The actual left modules of the original Jacobian algebra are equivalent
to the existing right modules of the reversed Jacobian algebra. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def oppositeJacobianLinearEquivalence (φ : Q.Potential k) :
    (Q.unrolledJacobianZAlgebra k φ).Obj ≌
      (Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).Objᵒᵖ :=
  (Q.oppositeReflectedJacobianIso k φ).linearEquivalence.trans
    ((Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).reflectedLinearEquivalence
      ((Q.vertices : ℤ)-1))

instance oppositeJacobianLinearEquivalenceFunctorLinear (φ : Q.Potential k) :
    (Q.oppositeJacobianLinearEquivalence k φ).functor.Linear k := by
  dsimp [oppositeJacobianLinearEquivalence, ZAlgebra.Isomorphism.linearEquivalence,
    ZAlgebra.reflectedLinearEquivalence]
  infer_instance

instance oppositeJacobianLinearEquivalenceFunctorAdditive (φ : Q.Potential k) :
    (Q.oppositeJacobianLinearEquivalence k φ).functor.Additive := by
  dsimp [oppositeJacobianLinearEquivalence, ZAlgebra.Isomorphism.linearEquivalence,
    ZAlgebra.reflectedLinearEquivalence]
  infer_instance

noncomputable def oppositeJacobianLeftRightEquivalence (φ : Q.Potential k) :
    (Q.unrolledJacobianZAlgebra k φ).LeftModule ≌
      (Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).RightModule :=
  linearRepresentationEquivalence (k := k) (Q.oppositeJacobianLinearEquivalence k φ)

instance oppositeJacobianLeftRightEquivalenceFunctorLinear (φ : Q.Potential k) :
    (Q.oppositeJacobianLeftRightEquivalence k φ).functor.Linear k := by
  change (linearRepresentationPrecomposition
    (k := k) (Q.oppositeJacobianLinearEquivalence k φ)).Linear k
  infer_instance

instance oppositeJacobianLeftRightEquivalenceFunctorAdditive (φ : Q.Potential k) :
    (Q.oppositeJacobianLeftRightEquivalence k φ).functor.Additive := by
  change (linearRepresentationPrecomposition
    (k := k) (Q.oppositeJacobianLinearEquivalence k φ)).Additive
  infer_instance

end ASGinzburg.CutQuiver
