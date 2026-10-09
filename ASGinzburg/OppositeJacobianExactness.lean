import ASGinzburg.OppositeJacobianLinearEquivalence
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! Short exact sequences of the existing Jacobian left and right modules
are preserved in both directions by the proved actual equivalence. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
universe u
variable (Q : CutQuiver) (k : Type u) [Field k] (φ : Q.Potential k)

theorem oppositeJacobianLeftRight_shortExact
    (S : ShortComplex (Q.unrolledJacobianZAlgebra k φ).LeftModule)
    (hS : S.ShortExact) :
    (S.map (Q.oppositeJacobianLeftRightEquivalence k φ).functor).ShortExact :=
  hS.map_of_exact _

theorem oppositeJacobianRightLeft_shortExact
    (S : ShortComplex
      (Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).RightModule)
    (hS : S.ShortExact) :
    (S.map (Q.oppositeJacobianLeftRightEquivalence k φ).inverse).ShortExact :=
  hS.map_of_exact _

theorem oppositeJacobianLeftRight_exact
    (S : ShortComplex (Q.unrolledJacobianZAlgebra k φ).LeftModule)
    (hS : S.Exact) :
    (S.map (Q.oppositeJacobianLeftRightEquivalence k φ).functor).Exact :=
  hS.map _

theorem oppositeJacobianRightLeft_exact
    (S : ShortComplex
      (Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).RightModule)
    (hS : S.Exact) :
    (S.map (Q.oppositeJacobianLeftRightEquivalence k φ).inverse).Exact :=
  hS.map _

end ASGinzburg.CutQuiver
