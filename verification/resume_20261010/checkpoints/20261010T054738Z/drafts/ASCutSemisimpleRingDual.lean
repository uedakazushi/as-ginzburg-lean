import work.ASGinzburgDraft.SplitQuotientRingDualCanonical
import ASGinzburg.ASCutSemisimpleTorFinite

/-! Original AS data identify the field dual of the actual right radical
quotient with the actual left radical quotient, by vertex evaluation. -/
namespace ASGinzburg.ZAlgebra
open scoped ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def ASRegular.cutSemisimpleRightDualLeftEquiv (hAS : A.ASRegular Q) :
    BalancedTensorHom k (hAS.CutGradedAlgebra A Q) (hAS.cutSemisimpleRightObject A Q) k ≃ₗ[
      hAS.CutGradedAlgebra A Q] (hAS.cutSemisimpleLeftObject A Q) := by
  classical
  exact splitQuotientCanonicalDualLeftLinearEquiv k (hAS.CutGradedAlgebra A Q)
    (hAS.cutGradedRadical A Q) Q.Vertex (hAS.cutGradedRadicalQuotientAlgEquiv A Q)

end ASGinzburg.ZAlgebra
