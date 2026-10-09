import ASGinzburg.OppositeJacobianExactness
import ASGinzburg.LinearCoyonedaPrecomposition
import ASGinzburg.OppositeCoyonedaYoneda

/-! The proved actual left/right Jacobian equivalence takes the original
left representable at i to the reversed right representable at n-1-i. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k] (φ : Q.Potential k)

noncomputable def oppositeJacobianLeftRepresentableIso (i : ℤ) :
    (Q.oppositeJacobianLeftRightEquivalence k φ).functor.obj
      ((Q.unrolledJacobianZAlgebra k φ).leftRepresentable i) ≅
        (Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).representable
          ((Q.vertices : ℤ)-1-i) :=
  ObjectProperty.isoMk _
    (linearCoyonedaPrecompositionIso (k := k) (Q.oppositeJacobianLinearEquivalence k φ) ⟨i⟩ ≪≫
      (Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).oppositeCoyonedaYonedaIso
        ((Q.vertices : ℤ)-1-i))

end ASGinzburg.CutQuiver
