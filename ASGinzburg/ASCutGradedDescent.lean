import ASGinzburg.PeriodCutDegreeZero
import ASGinzburg.FoundationPeriodRingRecovery

/-! The original AS condition provides the period used for the actual
cut-graded k-algebra. Its zero degree recovers the foundation and the
candidate's non-cut Jacobian ring. No period is an extra hypothesis. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

abbrev ASRegular.CutGradedPiece (hAS : A.ASRegular Q) (m : ℕ) :=
  (hAS.periodIso A Q).CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) m

abbrev ASRegular.CutGradedAlgebra (hAS : A.ASRegular Q) :=
  (hAS.periodIso A Q).CutGradedRing (fun i : Q.Vertex => (i.val : ℤ))

noncomputable instance ASRegular.cutGradedPieceFinite (hAS : A.ASRegular Q) (m : ℕ) :
    Module.Finite k (hAS.CutGradedPiece A Q m) := by
  change Module.Finite k (∀ i j : Q.Vertex, A.Hom (i.val : ℤ)
    ((j.val : ℤ)+(m:ℤ)*(Q.vertices:ℤ)))
  infer_instance

noncomputable def ASRegular.cutGradedInclusion (hAS : A.ASRegular Q) (m : ℕ) :
    hAS.CutGradedPiece A Q m →ₗ[k] hAS.CutGradedAlgebra A Q :=
  (hAS.periodIso A Q).cutHomogeneousLinearInclusion (fun i : Q.Vertex => (i.val : ℤ)) m

theorem ASRegular.cutGradedInclusion_mul (hAS : A.ASRegular Q) (m n : ℕ)
    (x : hAS.CutGradedPiece A Q m) (y : hAS.CutGradedPiece A Q n) :
    hAS.cutGradedInclusion A Q m x * hAS.cutGradedInclusion A Q n y=
      hAS.cutGradedInclusion A Q (m+n)
        ((hAS.periodIso A Q).cutBlockMul (fun i : Q.Vertex => (i.val : ℤ)) m n x y) :=
  (hAS.periodIso A Q).cutHomogeneousInclusion_mul _ m n x y

section Foundation
variable {A : ZAlgebra.{u,u} k} (hAS : A.ASRegular Q)

noncomputable def ASRegular.cutDegreeZeroFoundationAlgEquiv :
    hAS.CutGradedPiece A Q 0 ≃ₐ[k] A.FoundationAlgebra Q :=
  (hAS.periodIso A Q).cutDegreeZeroFoundationAlgEquiv Q

noncomputable def ASRegular.cutDegreeZeroJacobianAlgEquiv :
    Q.ZeroCutJacobianRing k (hAS.foundationPotential A Q) ≃ₐ[k] hAS.CutGradedPiece A Q 0 :=
  (hAS.foundationPeriodJacobianRingAlgEquiv A Q).trans
    (hAS.cutDegreeZeroFoundationAlgEquiv Q).symm

end Foundation
end ASGinzburg.ZAlgebra
