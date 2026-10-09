import ASGinzburg.OppositeJacobianModuleComponents
import ASGinzburg.RightSingleSupportIsomorphism

/-! The proved actual equivalence takes the existing simple quotients to
the existing reflected simple quotients, using their proved components. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
universe u
variable (Q : CutQuiver) (k : Type u) [Field k] (φ : Q.Potential k)

theorem oppositeJacobianLeftSimple_off_diagonal (i j : ℤ)
    (hj : j ≠ (Q.vertices : ℤ)-1-i) :
    IsZero (((Q.oppositeJacobianLeftRightEquivalence k φ).functor.obj
      ((Q.unrolledJacobianZAlgebra k φ).simpleLeftModule i)).obj.obj
        (Opposite.op (⟨j⟩ : (Q.opposite.unrolledJacobianZAlgebra k
          (Q.oppositePotentialEquiv k φ)).Obj))) := by
  have h : (Q.vertices : ℤ)-1-j ≠ i := by omega
  exact ((Q.unrolledJacobianZAlgebra k φ).simpleLeftModule_off_diagonal i _ h).of_iso
    (Q.oppositeJacobianLeftRightEvaluationIso k φ _ j)

noncomputable def oppositeJacobianLeftSimpleDiagonalIso (i : ℤ) :
    ((Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).rightModuleEvaluation
      ((Q.vertices : ℤ)-1-i)).obj
        ((Q.oppositeJacobianLeftRightEquivalence k φ).functor.obj
          ((Q.unrolledJacobianZAlgebra k φ).simpleLeftModule i)) ≅
      ((Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).rightModuleEvaluation
        ((Q.vertices : ℤ)-1-i)).obj
          ((Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).simpleRightModule
            ((Q.vertices : ℤ)-1-i)) := by
  let A := Q.unrolledJacobianZAlgebra k φ
  let B := Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)
  let M := A.simpleLeftModule i
  have hi : (Q.vertices : ℤ)-1-((Q.vertices : ℤ)-1-i)=i := by ring
  exact Q.oppositeJacobianLeftRightEvaluationIso k φ M ((Q.vertices : ℤ)-1-i) ≪≫
    eqToIso (congrArg (fun t => M.obj.obj (⟨t⟩ : A.Obj)) hi) ≪≫
    A.simpleLeftModuleDiagonalIso i ≪≫ (A.scalarEndEquiv i).symm.toModuleIso ≪≫
    (B.scalarEndEquiv ((Q.vertices : ℤ)-1-i)).toModuleIso ≪≫
    (B.simpleRightModuleDiagonalIso ((Q.vertices : ℤ)-1-i)).symm

noncomputable def oppositeJacobianLeftSimpleIso (i : ℤ) :
    (Q.oppositeJacobianLeftRightEquivalence k φ).functor.obj
      ((Q.unrolledJacobianZAlgebra k φ).simpleLeftModule i) ≅
        (Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).simpleRightModule
          ((Q.vertices : ℤ)-1-i) :=
  (Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).rightSingleSupportIso
    ((Q.vertices : ℤ)-1-i) _ _
    (Q.oppositeJacobianLeftSimple_off_diagonal k φ i)
    (fun j hj => (Q.opposite.unrolledJacobianZAlgebra k
      (Q.oppositePotentialEquiv k φ)).simpleRightModule_off_diagonal _ j hj)
    (Q.oppositeJacobianLeftSimpleDiagonalIso k φ i)

noncomputable def oppositeJacobianRightSimpleInverseIso (i : ℤ) :
    (Q.oppositeJacobianLeftRightEquivalence k φ).inverse.obj
      ((Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).simpleRightModule
        ((Q.vertices : ℤ)-1-i)) ≅ (Q.unrolledJacobianZAlgebra k φ).simpleLeftModule i :=
  ((Q.oppositeJacobianLeftRightEquivalence k φ).inverse.mapIso
    (Q.oppositeJacobianLeftSimpleIso k φ i)).symm ≪≫
    ((Q.oppositeJacobianLeftRightEquivalence k φ).unitIso.app _).symm

noncomputable def oppositeJacobianRightRepresentableInverseIso (i : ℤ) :
    (Q.oppositeJacobianLeftRightEquivalence k φ).inverse.obj
      ((Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).representable
        ((Q.vertices : ℤ)-1-i)) ≅ (Q.unrolledJacobianZAlgebra k φ).leftRepresentable i :=
  ((Q.oppositeJacobianLeftRightEquivalence k φ).inverse.mapIso
    (Q.oppositeJacobianLeftRepresentableIso k φ i)).symm ≪≫
    ((Q.oppositeJacobianLeftRightEquivalence k φ).unitIso.app _).symm

end ASGinzburg.CutQuiver
