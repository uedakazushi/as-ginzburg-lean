import work.ASGinzburgDraft.MinimalRelationRepresentativeIndependence
import work.ASGinzburgDraft.TriangleASArrowEvaluations
import work.ASGinzburgDraft.TriangleCutZDerivativeCoordinates
import ASGinzburg.ASFoundationPotentialDerivatives
import ASGinzburg.ASZeroCutRelationComparison

/-! The actual chosen foundation cut relations are independent and
lie in the genuine chosen AS quadratic evaluation kernel. -/
namespace ASGinzburg

def triangleFoundationRelationArrowEquiv :
    triangle333.FoundationRelationArrow 0 2 ≃ Fin 3 where
  toFun a := ⟨a.val.val - 6, by
    have ha : 6 ≤ a.val.val := by
      simpa only [triangle333, decide_eq_true_eq] using a.property.2.2
    have h9 : a.val.val < 9 := a.val.isLt
    omega⟩
  invFun z := ⟨triangleZ z, triangleZ_source_two z, triangleZ_target_zero z, triangleZ_cut z⟩
  left_inv a := by
    apply Subtype.ext
    apply Fin.ext
    have ha : 6 ≤ a.val.val := by
      simpa only [triangle333, decide_eq_true_eq] using a.property.2.2
    dsimp [triangleZ]
    omega
  right_inv z := by
    apply Fin.ext
    dsimp [triangleZ]
    omega

end ASGinzburg

namespace ASGinzburg.ZAlgebra
universe u
variable {k : Type u} [Field k] (A : ZAlgebra.{u,u} k)

noncomputable def ASRegular.triangleFoundationZRelation (hAS : A.ASRegular triangle333)
    (z : Fin 3) : triangle333.pathCutComponent k 0 2 0 :=
  hAS.foundationZeroCutRelation A triangle333 0 2 (triangleFoundationRelationArrowEquiv.symm z)

theorem ASRegular.triangleFoundationZRelation_val_linearIndependent
    (hAS : A.ASRegular triangle333) :
    LinearIndependent k (fun z => (hAS.triangleFoundationZRelation A z).val) := by
  let result := (hAS.foundationPathRelation_linearIndependent A triangle333 0 2).comp
    triangleFoundationRelationArrowEquiv.symm triangleFoundationRelationArrowEquiv.symm.injective
  exact result

theorem ASRegular.triangleFoundationZRelation_linearIndependent
    (hAS : A.ASRegular triangle333) :
    LinearIndependent k (hAS.triangleFoundationZRelation A) := by
  let result := LinearIndependent.of_comp (v := hAS.triangleFoundationZRelation A)
    (triangle333.pathCutComponent k 0 2 0).subtype
    (hAS.triangleFoundationZRelation_val_linearIndependent A)
  exact result

theorem ASRegular.triangleFoundationZRelation_evaluation_zero
    (hAS : A.ASRegular triangle333) (z : Fin 3) :
    hAS.triangleXYPathEvaluation A (hAS.triangleFoundationZRelation A z) = 0 := by
  change A.unrolledPathLinearEvaluation triangle333 (hAS.resolution A triangle333) (0,0) (2,0)
    (triangle333.zeroCutNativeUnrollingEquiv k 0 2
      (hAS.foundationZeroCutRelation A triangle333 0 2
        (triangleFoundationRelationArrowEquiv.symm z))) = 0
  rw [hAS.foundationZeroCutRelation_native A triangle333]
  exact (hAS.foundationRelationNative A triangle333 0 2
    (triangleFoundationRelationArrowEquiv.symm z)).property

theorem ASRegular.triangleFoundationZRelation_eq_derivative
    (hAS : A.ASRegular triangle333) (z : Fin 3) :
    hAS.triangleFoundationZRelation A z =
      triangleCutZDerivative k (hAS.foundationPotential A triangle333) z := by
  apply Subtype.ext
  change (hAS.triangleFoundationZRelation A z).val =
    triangle333.transportPathComponent k (triangleZ_target_zero z) (triangleZ_source_two z)
      (triangle333.pathCyclicDerivative k (triangleZ z) (hAS.foundationPotential A triangle333))
  rw [hAS.foundationPotential_pathCyclicDerivative A triangle333
    ⟨triangleZ z, triangleZ_cut z⟩]
  fin_cases z <;> rfl

end ASGinzburg.ZAlgebra
