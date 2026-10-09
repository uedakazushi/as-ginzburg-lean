import ASGinzburg.PathCyclicHessian
import ASGinzburg.OppositePathCyclicDerivative

/-! Reversal transposes the actual path-valued cyclic Hessian matrix. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem oppositePathComponentEquiv_cyclicHessian
    (a b : Q.Arrow) (φ : Q.Potential k) :
    Q.oppositePathComponentEquiv k (Q.target a) (Q.source b)
        (Q.pathCyclicHessian k a b φ) =
      Q.opposite.pathCyclicHessian k b a (Q.oppositePotentialEquiv k φ) := by
  apply Q.opposite.pathWordMap_injective k (Q.source b).rev (Q.target a).rev
  rw [Q.oppositePathComponentEquiv_wordMap,Q.pathWordMap_pathCyclicHessian]
  change reverseWordPolynomial (cyclicHessianWord a b φ.val) =
    Q.opposite.pathWordMap k (Q.opposite.target b) (Q.opposite.source a)
      (Q.opposite.pathCyclicHessian k b a (Q.oppositePotentialEquiv k φ))
  rw [Q.opposite.pathWordMap_pathCyclicHessian,oppositePotentialEquiv_val]
  exact (cyclicHessianWord_reverse a b φ.val).symm

end ASGinzburg.CutQuiver
