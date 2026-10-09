import ASGinzburg.PeriodCutGradedJacobson
import ASGinzburg.ASCutGradedDescent

/-! The original AS conditions alone supply the cut algebra whose actual
graded radical quotient is the vertex scalar algebra. No period or
semisimple-quotient hypothesis is added. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def ASRegular.cutGradedRadical (hAS : A.ASRegular Q) :
    Ideal (hAS.CutGradedAlgebra A Q) := (hAS.periodIso A Q).cutGradedJacobson Q

noncomputable instance ASRegular.cutGradedRadicalTwoSided (hAS : A.ASRegular Q) :
    (hAS.cutGradedRadical A Q).IsTwoSided :=
  (hAS.periodIso A Q).cutGradedJacobsonTwoSided Q

noncomputable def ASRegular.cutGradedRadicalQuotientAlgEquiv (hAS : A.ASRegular Q) :
    (hAS.CutGradedAlgebra A Q ⧸ hAS.cutGradedRadical A Q) ≃ₐ[k] (Q.Vertex→k) :=
  (hAS.periodIso A Q).cutGradedSemisimpleQuotientAlgEquiv Q

end ASGinzburg.ZAlgebra
