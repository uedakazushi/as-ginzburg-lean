import ASGinzburg.GinzburgCutJacobianProducts

/-! The actual fixed-cut degree-zero boundary quotient identifies
multiplicatively with the existing unrolled Jacobian algebra components. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgCutZeroQuotientUnrolledEquiv (φ : Q.Potential k)
    (x y : Q.LiftVertex) :
    Q.GinzburgCutZeroQuotient k φ x y ≃ₗ[k]
      (Q.unrolledJacobianZAlgebra k φ).Hom (Q.height x) (Q.height y) :=
  (Q.ginzburgCutZeroQuotientJacobianEquiv k φ x.1 y.1 (y.2-x.2)).trans
    (Q.homogeneousJacobianUnrolledEquiv k φ x y)

theorem ginzburgCutZeroQuotientUnrolledEquiv_comp (φ : Q.Potential k)
    {x y v : Q.LiftVertex} (f : Q.GinzburgCutZeroQuotient k φ x y)
    (g : Q.GinzburgCutZeroQuotient k φ y v) :
    Q.ginzburgCutZeroQuotientUnrolledEquiv k φ x v
        (Q.ginzburgCutZeroQuotientComp k φ g f)=
      (Q.unrolledJacobianZAlgebra k φ).comp
        (Q.ginzburgCutZeroQuotientUnrolledEquiv k φ y v g)
        (Q.ginzburgCutZeroQuotientUnrolledEquiv k φ x y f) := by
  change Q.homogeneousJacobianUnrolledEquiv k φ x v
    (Q.ginzburgCutZeroQuotientJacobianEquiv k φ x.1 v.1 (v.2-x.2)
      (Q.ginzburgCutZeroQuotientComp k φ g f))=_
  rw [Q.ginzburgCutZeroQuotientJacobianEquiv_comp k φ]
  exact Q.homogeneousJacobianUnrolledEquiv_comp k φ _ _

theorem ginzburgCutZeroQuotientUnrolledEquiv_surjective (φ : Q.Potential k)
    (x y : Q.LiftVertex) :
    Function.Surjective (Q.ginzburgCutZeroQuotientUnrolledEquiv k φ x y) :=
  (Q.ginzburgCutZeroQuotientUnrolledEquiv k φ x y).surjective

end ASGinzburg.CutQuiver
