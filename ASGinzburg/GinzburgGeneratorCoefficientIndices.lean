import ASGinzburg.GinzburgGeneratorPrefixJacobian
import ASGinzburg.GinzburgGeneratorIndices
import ASGinzburg.GinzburgGeneratorUpperFiltration
import ASGinzburg.PeriodInverse

/-! The actual layer homology coefficients have precisely the original
AS-resolution index families. These are component isomorphisms; module
naturality and the standard differential comparison remain separate. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgOriginalCoefficientFamilyEquiv (φ : Q.Potential k)
    (x v : Q.LiftVertex) :
    (Π a : Q.GinzburgIncomingDegree v.1 0,
      (Q.unrolledJacobianZAlgebra k φ).Hom (Q.height x)
        (Q.height (a.val.source Q,x.2+(v.2-x.2-a.val.cutDegree Q)))) ≃ₗ[k]
    (Π a : Q.incomingArrows v,
      (Q.unrolledJacobianZAlgebra k φ).Hom (Q.height x) (Q.height (Q.incomingSource v a))) :=
  (LinearEquiv.piCongrLeft k (fun a : Q.GinzburgIncomingDegree v.1 0 =>
    (Q.unrolledJacobianZAlgebra k φ).Hom (Q.height x)
      (Q.height (a.val.source Q,x.2+(v.2-x.2-a.val.cutDegree Q))))
        (Q.ginzburgOriginalGeneratorEquiv v)).symm.trans
    (LinearEquiv.piCongrRight fun a => (Q.unrolledJacobianZAlgebra k φ).homTransport _ _ _ _
      rfl (congrArg Q.height (Q.ginzburgOriginalGeneratorPrefixLift x v a)))

noncomputable def ginzburgDualCoefficientFamilyEquiv (φ : Q.Potential k)
    (x v : Q.LiftVertex) :
    (Π a : Q.GinzburgIncomingDegree v.1 (-1),
      (Q.unrolledJacobianZAlgebra k φ).Hom (Q.height x)
        (Q.height (a.val.source Q,x.2+(v.2-x.2-a.val.cutDegree Q)))) ≃ₗ[k]
    (Π a : Q.outgoingArrows (Q.tau.symm v),
      (Q.unrolledJacobianZAlgebra k φ).Hom (Q.height x)
        (Q.height (Q.outgoingTarget (Q.tau.symm v) a))) :=
  (LinearEquiv.piCongrLeft k (fun a : Q.GinzburgIncomingDegree v.1 (-1) =>
    (Q.unrolledJacobianZAlgebra k φ).Hom (Q.height x)
      (Q.height (a.val.source Q,x.2+(v.2-x.2-a.val.cutDegree Q))))
        (Q.ginzburgDualGeneratorEquiv v)).symm.trans
    (LinearEquiv.piCongrRight fun a => (Q.unrolledJacobianZAlgebra k φ).homTransport _ _ _ _
      rfl (congrArg Q.height (Q.ginzburgDualGeneratorPrefixLift x v a)))

noncomputable def ginzburgLoopCoefficientFamilyEquiv (φ : Q.Potential k)
    (x v : Q.LiftVertex) :
    (Π a : Q.GinzburgIncomingDegree v.1 (-2),
      (Q.unrolledJacobianZAlgebra k φ).Hom (Q.height x)
        (Q.height (a.val.source Q,x.2+(v.2-x.2-a.val.cutDegree Q)))) ≃ₗ[k]
      (Q.unrolledJacobianZAlgebra k φ).Hom (Q.height x) (Q.height (Q.tau.symm v)) :=
  ((LinearEquiv.piCongrLeft k (fun a : Q.GinzburgIncomingDegree v.1 (-2) =>
    (Q.unrolledJacobianZAlgebra k φ).Hom (Q.height x)
      (Q.height (a.val.source Q,x.2+(v.2-x.2-a.val.cutDegree Q))))
        (Q.ginzburgLoopGeneratorEquiv v)).symm.trans
    (LinearEquiv.piCongrRight fun a => (Q.unrolledJacobianZAlgebra k φ).homTransport _ _ _ _
      rfl (congrArg Q.height (Q.ginzburgLoopGeneratorPrefixLift x v a)))).trans
    (LinearEquiv.funUnique PUnit.{1} k _)

noncomputable def ginzburgOriginalLayerHomologyCoefficientIso (φ : Q.Potential k)
    (x v : Q.LiftVertex) :
    Q.ginzburgAssociatedGradedHomology k φ x.1 v.1 0 (v.2-x.2) 0 ≅
      ModuleCat.of k (Π a : Q.incomingArrows v,
        (Q.unrolledJacobianZAlgebra k φ).Hom (Q.height x) (Q.height (Q.incomingSource v a))) :=
  Q.ginzburgAssociatedGradedTopHomologyUnrolledIso k φ x v.1 0 (v.2-x.2) ≪≫
    (Q.ginzburgOriginalCoefficientFamilyEquiv k φ x v).toModuleIso
      (g₁ := Pi.addCommGroup) (g₂ := Pi.addCommGroup)

noncomputable def ginzburgDualLayerHomologyCoefficientIso (φ : Q.Potential k)
    (x v : Q.LiftVertex) :
    Q.ginzburgAssociatedGradedHomology k φ x.1 v.1 (-1) (v.2-x.2) (-1) ≅
      ModuleCat.of k (Π a : Q.outgoingArrows (Q.tau.symm v),
        (Q.unrolledJacobianZAlgebra k φ).Hom (Q.height x)
          (Q.height (Q.outgoingTarget (Q.tau.symm v) a))) :=
  Q.ginzburgAssociatedGradedTopHomologyUnrolledIso k φ x v.1 (-1) (v.2-x.2) ≪≫
    (Q.ginzburgDualCoefficientFamilyEquiv k φ x v).toModuleIso
      (g₁ := Pi.addCommGroup) (g₂ := Pi.addCommGroup)

noncomputable def ginzburgLoopLayerHomologyCoefficientIso (φ : Q.Potential k)
    (x v : Q.LiftVertex) :
    Q.ginzburgAssociatedGradedHomology k φ x.1 v.1 (-2) (v.2-x.2) (-2) ≅
      ModuleCat.of k ((Q.unrolledJacobianZAlgebra k φ).Hom (Q.height x) (Q.height (Q.tau.symm v))) :=
  Q.ginzburgAssociatedGradedTopHomologyUnrolledIso k φ x v.1 (-2) (v.2-x.2) ≪≫
    (Q.ginzburgLoopCoefficientFamilyEquiv k φ x v).toModuleIso (g₁ := Pi.addCommGroup)

noncomputable def ginzburgUpperFilteredHomologyCoefficientIso (φ : Q.Potential k)
    (x v : Q.LiftVertex) :
    Q.ginzburgGeneratorFilteredHomology k φ x.1 v.1 0 (v.2-x.2) 0 ≅
      ModuleCat.of k (Π a : Q.incomingArrows v,
        (Q.unrolledJacobianZAlgebra k φ).Hom (Q.height x) (Q.height (Q.incomingSource v a))) :=
  Q.ginzburgGeneratorFilteredZeroHomologyIso k φ x.1 v.1 (v.2-x.2) 0 ≪≫
    Q.ginzburgOriginalLayerHomologyCoefficientIso k φ x v

end ASGinzburg.CutQuiver
