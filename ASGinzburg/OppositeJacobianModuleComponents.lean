import ASGinzburg.OppositeJacobianRepresentables
import ASGinzburg.ZAlgebraObjectRigidity

/-! The actual inverse category equivalence has the required reflected
integer indices, so the actual left/right module equivalence has the
required evaluation components. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory Opposite
universe u
variable (Q : CutQuiver) (k : Type u) [Field k] (φ : Q.Potential k)

theorem oppositeJacobianLinearEquivalence_inverse_index (j : ℤ) :
    ((Q.oppositeJacobianLinearEquivalence k φ).inverse.obj
      (op (⟨j⟩ : (Q.opposite.unrolledJacobianZAlgebra k
        (Q.oppositePotentialEquiv k φ)).Obj))).index = (Q.vertices : ℤ)-1-j := by
  let E := Q.oppositeJacobianLinearEquivalence k φ
  let B := Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)
  have h := B.objIndex_eq_of_iso ((E.counitIso.app (op ⟨j⟩)).unop)
  change j = (Q.vertices : ℤ)-1-(E.inverse.obj (op ⟨j⟩)).index at h
  change (E.inverse.obj (op ⟨j⟩)).index = (Q.vertices : ℤ)-1-j
  omega

theorem oppositeJacobianLinearEquivalence_inverse_obj (j : ℤ) :
    (Q.oppositeJacobianLinearEquivalence k φ).inverse.obj
      (op (⟨j⟩ : (Q.opposite.unrolledJacobianZAlgebra k
        (Q.oppositePotentialEquiv k φ)).Obj)) = ⟨(Q.vertices : ℤ)-1-j⟩ := by
  have h := Q.oppositeJacobianLinearEquivalence_inverse_index k φ j
  cases hx : (Q.oppositeJacobianLinearEquivalence k φ).inverse.obj
      (op (⟨j⟩ : (Q.opposite.unrolledJacobianZAlgebra k
        (Q.oppositePotentialEquiv k φ)).Obj)) with
  | mk a =>
    simp only [hx] at h
    exact congrArg ZAlgebra.Obj.mk h

noncomputable def oppositeJacobianLeftRightEvaluationIso
    (M : (Q.unrolledJacobianZAlgebra k φ).LeftModule) (j : ℤ) :
    ((Q.oppositeJacobianLeftRightEquivalence k φ).functor.obj M).obj.obj
      (op (⟨j⟩ : (Q.opposite.unrolledJacobianZAlgebra k
        (Q.oppositePotentialEquiv k φ)).Obj)) ≅
      M.obj.obj ⟨(Q.vertices : ℤ)-1-j⟩ :=
  eqToIso (congrArg M.obj.obj (Q.oppositeJacobianLinearEquivalence_inverse_obj k φ j))

end ASGinzburg.CutQuiver
