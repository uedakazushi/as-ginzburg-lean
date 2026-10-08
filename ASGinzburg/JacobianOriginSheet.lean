import ASGinzburg.JacobianUnrollingQuotient

/-! Homogeneous Jacobian coefficients with an arbitrary integer origin
sheet, as needed for every component of the genuine module resolution. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def homogeneousJacobianOriginSheetEquiv (φ : Q.Potential k)
    (x : Q.LiftVertex) (v : Q.Vertex) (c : ℤ) :
    (Q.pathCutComponent k x.1 v c ⧸ Q.pathJacobianCutIdeal k φ x.1 v c) ≃ₗ[k]
      (Q.unrolledJacobianZAlgebra k φ).Hom (Q.height x) (Q.height (v,x.2+c)) := by
  have e := Q.homogeneousJacobianUnrolledEquiv k φ x (v,x.2+c)
  rw [show x.2+c-x.2=c by omega] at e
  exact e

end ASGinzburg.CutQuiver
