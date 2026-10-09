import ASGinzburg.OppositeUnrolledJacobianHom
import ASGinzburg.ReflectedZAlgebra

/-! The lifted anti-multiplicative maps are multiplicative maps into
the actual reflected opposite algebra, with all indices transported explicitly. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def oppositeReflectedJacobianComponentEquiv (φ : Q.Potential k)
    (u v : Q.LiftVertex) :
    (Q.unrolledJacobianZAlgebra k φ).Hom (Q.height u) (Q.height v) ≃ₗ[k]
      ((Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).reflected
        ((Q.vertices : ℤ)-1)).Hom (Q.height u) (Q.height v) :=
  (Q.oppositeUnrolledJacobianHomEquiv k φ u v).trans
    ((Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).homTransport
      _ _ _ _ (Q.oppositeLiftVertexEquiv_height v) (Q.oppositeLiftVertexEquiv_height u))

theorem oppositeReflectedJacobianComponentEquiv_comp (φ : Q.Potential k)
    {u v w : Q.LiftVertex}
    (f : (Q.unrolledJacobianZAlgebra k φ).Hom (Q.height u) (Q.height v))
    (g : (Q.unrolledJacobianZAlgebra k φ).Hom (Q.height v) (Q.height w)) :
    Q.oppositeReflectedJacobianComponentEquiv k φ u w ((Q.unrolledJacobianZAlgebra k φ).comp g f) =
      ((Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).reflected
        ((Q.vertices : ℤ)-1)).comp
        (Q.oppositeReflectedJacobianComponentEquiv k φ v w g)
        (Q.oppositeReflectedJacobianComponentEquiv k φ u v f) := by
  simp only [oppositeReflectedJacobianComponentEquiv, LinearEquiv.trans_apply,
    ZAlgebra.reflected_comp]
  rw [Q.oppositeUnrolledJacobianHomEquiv_comp]
  exact (Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).homTransport_comp
    _ _ _ _ _ _ (Q.oppositeLiftVertexEquiv_height w)
    (Q.oppositeLiftVertexEquiv_height v) (Q.oppositeLiftVertexEquiv_height u)
    (Q.oppositeUnrolledJacobianHomEquiv k φ v w g)
    (Q.oppositeUnrolledJacobianHomEquiv k φ u v f)

theorem oppositeReflectedJacobianComponentEquiv_id (φ : Q.Potential k) (v : Q.LiftVertex) :
    Q.oppositeReflectedJacobianComponentEquiv k φ v v ((Q.unrolledJacobianZAlgebra k φ).id (Q.height v)) =
      ((Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).reflected
        ((Q.vertices : ℤ)-1)).id (Q.height v) := by
  simp only [oppositeReflectedJacobianComponentEquiv, LinearEquiv.trans_apply]
  rw [Q.oppositeUnrolledJacobianHomEquiv_id]
  exact (Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).homTransport_id
    _ _ (Q.oppositeLiftVertexEquiv_height v)

end ASGinzburg.CutQuiver
