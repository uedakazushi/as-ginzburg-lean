import ASGinzburg.GinzburgCutQuotientUnrolledProducts
import ASGinzburg.OppositeUnrolledJacobianHom

/-! Actual ordinary-path classes identify the degree-zero Ginzburg quotient
with the Jacobian components and reflect by actual path reversal. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgJacobianPathClass (φ : Q.Potential k)
    (x y : Q.LiftVertex) (f : Q.pathCutComponent k x.1 y.1 (y.2-x.2)) :
    (Q.unrolledJacobianZAlgebra k φ).Hom (Q.height x) (Q.height y) :=
  Q.homogeneousJacobianUnrolledEquiv k φ x y (Submodule.Quotient.mk f)

theorem ginzburgCutZeroQuotientUnrolledEquiv_original_mk (φ : Q.Potential k)
    (x y : Q.LiftVertex) (f : Q.pathCutComponent k x.1 y.1 (y.2-x.2)) :
    Q.ginzburgCutZeroQuotientUnrolledEquiv k φ x y
      (Submodule.Quotient.mk (Q.originalGinzburgCutDegreeZeroEquiv k x.1 y.1 (y.2-x.2) f))=
      Q.ginzburgJacobianPathClass k φ x y f := by
  change Q.homogeneousJacobianUnrolledEquiv k φ x y
    (Q.ginzburgCutZeroQuotientJacobianEquiv k φ x.1 y.1 (y.2-x.2)
      (Submodule.Quotient.mk _))=_
  rw [Q.ginzburgCutZeroQuotientJacobianEquiv_mk,LinearEquiv.symm_apply_apply]
  rfl

theorem ginzburgJacobianPathClass_opposite (φ : Q.Potential k)
    (x y : Q.LiftVertex) (f : Q.pathCutComponent k x.1 y.1 (y.2-x.2)) :
    Q.oppositeUnrolledJacobianHomEquiv k φ x y (Q.ginzburgJacobianPathClass k φ x y f)=
      Q.opposite.ginzburgJacobianPathClass k (Q.oppositePotentialEquiv k φ)
        (Q.oppositeLiftVertexEquiv y) (Q.oppositeLiftVertexEquiv x)
        (Q.oppositeBetweenSheetPathCutEquiv k x y f) := by
  simp only [ginzburgJacobianPathClass,oppositeUnrolledJacobianHomEquiv,
    LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply,
    Q.oppositeBetweenSheetJacobianEquiv_mk]

end ASGinzburg.CutQuiver
