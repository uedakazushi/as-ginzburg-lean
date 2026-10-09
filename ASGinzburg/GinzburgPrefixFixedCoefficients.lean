import ASGinzburg.GinzburgPrefixFamilyClasses
import ASGinzburg.GinzburgCutQuotientUnrolledProducts
import ASGinzburg.GinzburgCutZeroQuotientTransports

/-! Prefix coefficient quotients are genuine A(Phi) components with
endpoints independent of the origin sheet. Only arithmetic transport is used. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

def ginzburgPrefixGeneratorEndpoint (v : Q.LiftVertex) (a : Q.GinzburgArrow) :
    Q.LiftVertex := (a.source Q,v.2-a.cutDegree Q)

noncomputable def ginzburgPrefixCoefficientCutEquiv (φ : Q.Potential k)
    (x v : Q.LiftVertex) (a : Q.GinzburgArrow) :
    (Q.ginzburgCutCohomologicalComponent k x.1 (a.source Q) 0 (v.2-x.2-a.cutDegree Q) ⧸
      LinearMap.range (Q.ginzburgCutNegativeOneDifferential k φ x.1 (a.source Q)
        (v.2-x.2-a.cutDegree Q))) ≃ₗ[k]
      Q.GinzburgCutZeroQuotient k φ x (Q.ginzburgPrefixGeneratorEndpoint v a) :=
  Q.ginzburgCutZeroQuotientEquivOfCutEq k φ x.1 (a.source Q)
    (v.2-x.2-a.cutDegree Q) ((v.2-a.cutDegree Q)-x.2) (by omega)

noncomputable def ginzburgPrefixCoefficientFixedUnrolledEquiv (φ : Q.Potential k)
    (x v : Q.LiftVertex) (a : Q.GinzburgArrow) :
    (Q.ginzburgCutCohomologicalComponent k x.1 (a.source Q) 0 (v.2-x.2-a.cutDegree Q) ⧸
      LinearMap.range (Q.ginzburgCutNegativeOneDifferential k φ x.1 (a.source Q)
        (v.2-x.2-a.cutDegree Q))) ≃ₗ[k]
      (Q.unrolledJacobianZAlgebra k φ).Hom (Q.height x)
        (Q.height (Q.ginzburgPrefixGeneratorEndpoint v a)) :=
  (Q.ginzburgPrefixCoefficientCutEquiv k φ x v a).trans
    (Q.ginzburgCutZeroQuotientUnrolledEquiv k φ x (Q.ginzburgPrefixGeneratorEndpoint v a))

noncomputable def ginzburgPrefixFixedQuotientFamilyEquiv (φ : Q.Potential k)
    (x v : Q.LiftVertex) (r : ℤ) :
    (Π a : {a : Q.GinzburgArrow // a.target Q=v.1 ∧ a.cohomologicalDegree Q=r},
      (Q.ginzburgCutCohomologicalComponent k x.1 (a.val.source Q) 0 (v.2-x.2-a.val.cutDegree Q) ⧸
        LinearMap.range (Q.ginzburgCutNegativeOneDifferential k φ x.1 (a.val.source Q)
          (v.2-x.2-a.val.cutDegree Q)))) ≃ₗ[k]
    (Π a : {a : Q.GinzburgArrow // a.target Q=v.1 ∧ a.cohomologicalDegree Q=r},
      (Q.unrolledJacobianZAlgebra k φ).Hom (Q.height x)
        (Q.height (Q.ginzburgPrefixGeneratorEndpoint v a.val))) :=
  LinearEquiv.piCongrRight fun a => Q.ginzburgPrefixCoefficientFixedUnrolledEquiv k φ x v a.val

end ASGinzburg.CutQuiver
