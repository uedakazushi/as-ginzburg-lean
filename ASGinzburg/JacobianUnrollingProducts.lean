import ASGinzburg.JacobianUnrollingQuotient
import ASGinzburg.JacobianCutQuotientProducts

/-! Actual homogeneous Jacobian/unrolling quotient comparison
preserves the bilinear products induced from genuine path products. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem homogeneousJacobianUnrolledEquiv_mk (φ : Q.Potential k) (u v : Q.LiftVertex)
    (f : Q.pathCutComponent k u.1 v.1 (v.2-u.2)) :
    Q.homogeneousJacobianUnrolledEquiv k φ u v (Submodule.Quotient.mk f)=
      Submodule.Quotient.mk (Q.unrolledComponentHeightEquiv k u v
        (Q.betweenSheetLinearEquiv k u v f)) := rfl

theorem homogeneousJacobianUnrolledEquiv_comp (φ : Q.Potential k)
    {u v w : Q.LiftVertex} (f : Q.PathCutJacobianQuotient k φ u v)
    (g : Q.PathCutJacobianQuotient k φ v w) :
    Q.homogeneousJacobianUnrolledEquiv k φ u w (Q.cutJacobianQuotientComp k φ g f)=
      (Q.unrolledJacobianZAlgebra k φ).comp
        (Q.homogeneousJacobianUnrolledEquiv k φ v w g)
          (Q.homogeneousJacobianUnrolledEquiv k φ u v f) := by
  obtain ⟨f,rfl⟩ := (Q.pathJacobianCutIdeal k φ u.1 v.1 (v.2-u.2)).mkQ_surjective f
  obtain ⟨g,rfl⟩ := (Q.pathJacobianCutIdeal k φ v.1 w.1 (w.2-v.2)).mkQ_surjective g
  change Q.homogeneousJacobianUnrolledEquiv k φ u w
    (Q.cutJacobianQuotientComp k φ (Submodule.Quotient.mk g) (Submodule.Quotient.mk f))=
      (Q.unrolledJacobianZAlgebra k φ).comp
        (Q.homogeneousJacobianUnrolledEquiv k φ v w (Submodule.Quotient.mk g))
        (Q.homogeneousJacobianUnrolledEquiv k φ u v (Submodule.Quotient.mk f))
  rw [Q.cutJacobianQuotientComp_mk,Q.homogeneousJacobianUnrolledEquiv_mk,
    Q.homogeneousJacobianUnrolledEquiv_mk,Q.homogeneousJacobianUnrolledEquiv_mk]
  change Submodule.Quotient.mk
    (Q.unrolledComponentHeightEquiv k u w
      (Q.betweenSheetLinearEquiv k u w (Q.pathCutCompBetween k g f)))=
    Submodule.Quotient.mk ((Q.unrolledPathZAlgebra k).comp
      (Q.unrolledComponentHeightEquiv k v w (Q.betweenSheetLinearEquiv k v w g))
      (Q.unrolledComponentHeightEquiv k u v (Q.betweenSheetLinearEquiv k u v f)))
  rw [Q.betweenSheetLinearEquiv_comp,Q.unrolledComponentHeightEquiv_comp]

end ASGinzburg.CutQuiver
