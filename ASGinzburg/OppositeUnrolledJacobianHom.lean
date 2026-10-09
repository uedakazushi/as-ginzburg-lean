import ASGinzburg.OppositeBetweenSheetJacobian
import ASGinzburg.JacobianUnrollingProducts

/-! Genuine anti-multiplicative comparison of all lifted Jacobian components. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def oppositeUnrolledJacobianHomEquiv (φ : Q.Potential k)
    (u v : Q.LiftVertex) :
    (Q.unrolledJacobianZAlgebra k φ).Hom (Q.height u) (Q.height v) ≃ₗ[k]
      (Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).Hom
        (Q.opposite.height (Q.oppositeLiftVertexEquiv v))
        (Q.opposite.height (Q.oppositeLiftVertexEquiv u)) :=
  (Q.homogeneousJacobianUnrolledEquiv k φ u v).symm.trans
    ((Q.oppositeBetweenSheetJacobianEquiv k φ u v).trans
      (Q.opposite.homogeneousJacobianUnrolledEquiv k (Q.oppositePotentialEquiv k φ)
        (Q.oppositeLiftVertexEquiv v) (Q.oppositeLiftVertexEquiv u)))

theorem oppositeUnrolledJacobianHomEquiv_comp (φ : Q.Potential k)
    {u v w : Q.LiftVertex}
    (f : (Q.unrolledJacobianZAlgebra k φ).Hom (Q.height u) (Q.height v))
    (g : (Q.unrolledJacobianZAlgebra k φ).Hom (Q.height v) (Q.height w)) :
    Q.oppositeUnrolledJacobianHomEquiv k φ u w ((Q.unrolledJacobianZAlgebra k φ).comp g f) =
      (Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).comp
        (Q.oppositeUnrolledJacobianHomEquiv k φ u v f)
        (Q.oppositeUnrolledJacobianHomEquiv k φ v w g) := by
  obtain ⟨f,rfl⟩ := (Q.homogeneousJacobianUnrolledEquiv k φ u v).surjective f
  obtain ⟨g,rfl⟩ := (Q.homogeneousJacobianUnrolledEquiv k φ v w).surjective g
  rw [← Q.homogeneousJacobianUnrolledEquiv_comp]
  simp only [oppositeUnrolledJacobianHomEquiv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]
  rw [Q.oppositeBetweenSheetJacobianEquiv_comp,
    Q.opposite.homogeneousJacobianUnrolledEquiv_comp]

theorem oppositeUnrolledJacobianHomEquiv_id (φ : Q.Potential k) (v : Q.LiftVertex) :
    Q.oppositeUnrolledJacobianHomEquiv k φ v v
        ((Q.unrolledJacobianZAlgebra k φ).id (Q.height v)) =
      (Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).id
        (Q.opposite.height (Q.oppositeLiftVertexEquiv v)) := by
  obtain ⟨f,hf⟩ := (Q.oppositeUnrolledJacobianHomEquiv k φ v v).surjective
    ((Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).id
      (Q.opposite.height (Q.oppositeLiftVertexEquiv v)))
  have he := Q.oppositeUnrolledJacobianHomEquiv_comp k φ
    ((Q.unrolledJacobianZAlgebra k φ).id (Q.height v)) f
  rw [ZAlgebra.id_comp, hf, ZAlgebra.id_comp] at he
  exact he.symm

end ASGinzburg.CutQuiver
