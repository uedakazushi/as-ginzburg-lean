import ASGinzburg.OppositeReflectedJacobianComponents
import ASGinzburg.ReindexedZAlgebraIsomorphism

/-! The actual Jacobian algebra is isomorphic to the reflected opposite
Jacobian algebra, on all integer indices and without regularity assumptions. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def oppositeReflectedJacobianIso (φ : Q.Potential k) :
    ZAlgebra.Isomorphism (Q.unrolledJacobianZAlgebra k φ)
      ((Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).reflected
        ((Q.vertices : ℤ)-1)) :=
  ZAlgebra.Isomorphism.ofSurjectiveReindex _ _ Q.height Q.height_bijective.2
    (Q.oppositeReflectedJacobianComponentEquiv k φ)
    (Q.oppositeReflectedJacobianComponentEquiv_id k φ)
    (fun _ _ _ f g => Q.oppositeReflectedJacobianComponentEquiv_comp k φ f g)

end ASGinzburg.CutQuiver
