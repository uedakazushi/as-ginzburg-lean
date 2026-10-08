import ASGinzburg.GinzburgGeneratorCoefficientIndices
import ASGinzburg.CoproductRadicals

/-! Actual component identifications with the existing finite projective
AS terms. No AS-resolution existence or module naturality is assumed. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def asResolutionTermOneComponentEquiv (w : Q.LiftVertex) (i : ℤ) :
    (A.rightModuleEvaluation i).obj (A.asResolutionTerm₁ Q w) ≃ₗ[k]
      (Π a : Q.incomingArrows w, A.Hom i (Q.height (Q.incomingSource w a))) :=
  A.rightFiniteCoproductPiEquiv
    (fun a : Q.incomingArrows w => A.representable (Q.height (Q.incomingSource w a))) i

noncomputable def asResolutionTermTwoComponentEquiv (w : Q.LiftVertex) (i : ℤ) :
    (A.rightModuleEvaluation i).obj (A.asResolutionTerm₂ Q w) ≃ₗ[k]
      (Π a : Q.outgoingArrows (Q.tau.symm w),
        A.Hom i (Q.height (Q.outgoingTarget (Q.tau.symm w) a))) :=
  A.rightFiniteCoproductPiEquiv
    (fun a : Q.outgoingArrows (Q.tau.symm w) =>
      A.representable (Q.height (Q.outgoingTarget (Q.tau.symm w) a))) i

end ASGinzburg.ZAlgebra

namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgOriginalLayerHomologyTermOneIso (φ : Q.Potential k)
    (x v : Q.LiftVertex) :
    Q.ginzburgAssociatedGradedHomology k φ x.1 v.1 0 (v.2-x.2) 0 ≅
      ((Q.unrolledJacobianZAlgebra k φ).rightModuleEvaluation (Q.height x)).obj
        ((Q.unrolledJacobianZAlgebra k φ).asResolutionTerm₁ Q v) :=
  Q.ginzburgOriginalLayerHomologyCoefficientIso k φ x v ≪≫
    ((Q.unrolledJacobianZAlgebra k φ).asResolutionTermOneComponentEquiv Q v
      (Q.height x)).toModuleIso.symm

noncomputable def ginzburgDualLayerHomologyTermTwoIso (φ : Q.Potential k)
    (x v : Q.LiftVertex) :
    Q.ginzburgAssociatedGradedHomology k φ x.1 v.1 (-1) (v.2-x.2) (-1) ≅
      ((Q.unrolledJacobianZAlgebra k φ).rightModuleEvaluation (Q.height x)).obj
        ((Q.unrolledJacobianZAlgebra k φ).asResolutionTerm₂ Q v) :=
  Q.ginzburgDualLayerHomologyCoefficientIso k φ x v ≪≫
    ((Q.unrolledJacobianZAlgebra k φ).asResolutionTermTwoComponentEquiv Q v
      (Q.height x)).toModuleIso.symm

noncomputable def ginzburgLoopLayerHomologyRepresentableIso (φ : Q.Potential k)
    (x v : Q.LiftVertex) :
    Q.ginzburgAssociatedGradedHomology k φ x.1 v.1 (-2) (v.2-x.2) (-2) ≅
      ((Q.unrolledJacobianZAlgebra k φ).rightModuleEvaluation (Q.height x)).obj
        ((Q.unrolledJacobianZAlgebra k φ).representable (Q.height (Q.tau.symm v))) :=
  Q.ginzburgLoopLayerHomologyCoefficientIso k φ x v

noncomputable def ginzburgUpperFilteredHomologyTermOneIso (φ : Q.Potential k)
    (x v : Q.LiftVertex) :
    Q.ginzburgGeneratorFilteredHomology k φ x.1 v.1 0 (v.2-x.2) 0 ≅
      ((Q.unrolledJacobianZAlgebra k φ).rightModuleEvaluation (Q.height x)).obj
        ((Q.unrolledJacobianZAlgebra k φ).asResolutionTerm₁ Q v) :=
  Q.ginzburgUpperFilteredHomologyCoefficientIso k φ x v ≪≫
    ((Q.unrolledJacobianZAlgebra k φ).asResolutionTermOneComponentEquiv Q v
      (Q.height x)).toModuleIso.symm

end ASGinzburg.CutQuiver
