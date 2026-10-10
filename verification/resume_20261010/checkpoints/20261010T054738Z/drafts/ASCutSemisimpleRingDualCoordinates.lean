import work.ASGinzburgDraft.ASCutSemisimpleRingDual

/-! Vertex coordinates and field linearity for the genuine AS
semisimple dual identification. -/
namespace ASGinzburg.ZAlgebra
open scoped ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def ASRegular.cutSemisimpleRightDualLeftFieldEquiv (hAS : A.ASRegular Q) :
    BalancedTensorHom k (hAS.CutGradedAlgebra A Q) (hAS.cutSemisimpleRightObject A Q) k ≃ₗ[k]
      (hAS.cutSemisimpleLeftObject A Q) :=
  (hAS.cutSemisimpleRightDualLeftEquiv A Q).restrictScalars k

noncomputable def ASRegular.cutSemisimpleRightVertexIdempotent (hAS : A.ASRegular Q)
    (i : Q.Vertex) : hAS.cutSemisimpleRightObject A Q := by
  classical
  exact splitQuotientVertexIdempotent k (hAS.CutGradedAlgebra A Q)
    (hAS.cutGradedRadical A Q) Q.Vertex (hAS.cutGradedRadicalQuotientAlgEquiv A Q) i

@[simp] theorem ASRegular.cutSemisimpleRightDualLeftEquiv_coordinate (hAS : A.ASRegular Q)
    (φ : BalancedTensorHom k (hAS.CutGradedAlgebra A Q) (hAS.cutSemisimpleRightObject A Q) k)
    (i : Q.Vertex) :
    hAS.cutGradedRadicalQuotientAlgEquiv A Q
        (hAS.cutSemisimpleRightDualLeftEquiv A Q φ) i =
      φ (hAS.cutSemisimpleRightVertexIdempotent A Q i) := by
  classical
  exact splitQuotientDualFieldEquiv_coordinate k (hAS.CutGradedAlgebra A Q)
    (hAS.cutGradedRadical A Q) Q.Vertex (hAS.cutGradedRadicalQuotientAlgEquiv A Q)
    (splitQuotientCanonicalDualFieldChange k (hAS.CutGradedAlgebra A Q)
      (hAS.cutGradedRadical A Q) φ) i

end ASGinzburg.ZAlgebra
