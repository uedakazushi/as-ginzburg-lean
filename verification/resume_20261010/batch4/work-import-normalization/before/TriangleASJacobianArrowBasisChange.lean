import work.ASGinzburgDraft.TriangleASArrowEvaluations

/-! Comparing the actual chosen AS path presentation with the canonical
Jacobian arrow presentation yields genuine invertible non-cut arrow maps. -/
namespace ASGinzburg
universe u
variable (k : Type u) [Field k] (φ : triangle333.Potential k)

noncomputable def triangleASJacobianXBasisChange
    (hAS : (triangle333.unrolledJacobianZAlgebra k φ).ASRegular triangle333) :
    ArrowSpace333 k ≃ₗ[k] ArrowSpace333 k :=
  (hAS.triangleXArrowEvaluationEquiv _).trans (triangleJacobianXArrowEquiv k φ).symm

noncomputable def triangleASJacobianYBasisChange
    (hAS : (triangle333.unrolledJacobianZAlgebra k φ).ASRegular triangle333) :
    ArrowSpace333 k ≃ₗ[k] ArrowSpace333 k :=
  (hAS.triangleYArrowEvaluationEquiv _).trans (triangleJacobianYArrowEquiv k φ).symm

theorem triangleASJacobianXBasisChange_commutes
    (hAS : (triangle333.unrolledJacobianZAlgebra k φ).ASRegular triangle333)
    (x : ArrowSpace333 k) :
    triangleJacobianXArrowEquiv k φ (triangleASJacobianXBasisChange k φ hAS x) =
      hAS.triangleXArrowEvaluation _ x :=
  (triangleJacobianXArrowEquiv k φ).apply_symm_apply _

theorem triangleASJacobianYBasisChange_commutes
    (hAS : (triangle333.unrolledJacobianZAlgebra k φ).ASRegular triangle333)
    (y : ArrowSpace333 k) :
    triangleJacobianYArrowEquiv k φ (triangleASJacobianYBasisChange k φ hAS y) =
      hAS.triangleYArrowEvaluation _ y :=
  (triangleJacobianYArrowEquiv k φ).apply_symm_apply _

end ASGinzburg
