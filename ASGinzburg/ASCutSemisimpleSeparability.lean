import ASGinzburg.ASCutGradedRadicalQuotient
import ASGinzburg.ScalarProductSeparability

/-! Original AS regularity gives actual separability of the actual
cut graded-radical quotient: all field base changes and its enveloping
algebra are semisimple, via genuine tensor algebra equivalences. -/
namespace ASGinzburg.ZAlgebra
open scoped TensorProduct
universe u v w
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def ASRegular.cutSemisimpleEnvelopingEquiv (hAS : A.ASRegular Q) :
    ((hAS.CutGradedAlgebra A Q ⧸ hAS.cutGradedRadical A Q) ⊗[k]
      (hAS.CutGradedAlgebra A Q ⧸ hAS.cutGradedRadical A Q)ᵐᵒᵖ) ≃ₐ[k] (Q.Vertex→Q.Vertex→k) :=
  (Algebra.TensorProduct.congr (hAS.cutGradedRadicalQuotientAlgEquiv A Q)
    (hAS.cutGradedRadicalQuotientAlgEquiv A Q).op).trans (scalarProductEnvelopingEquiv k Q.Vertex)

theorem ASRegular.cutSemisimpleEnveloping_isSemisimple (hAS : A.ASRegular Q) :
    IsSemisimpleRing ((hAS.CutGradedAlgebra A Q ⧸ hAS.cutGradedRadical A Q) ⊗[k]
      (hAS.CutGradedAlgebra A Q ⧸ hAS.cutGradedRadical A Q)ᵐᵒᵖ) :=
  (hAS.cutSemisimpleEnvelopingEquiv A Q).symm.toRingEquiv.isSemisimpleRing

noncomputable def ASRegular.cutSemisimpleBaseChangeEquiv (hAS : A.ASRegular Q)
    (K : Type w) [Field K] [Algebra k K] :
    (K ⊗[k] (hAS.CutGradedAlgebra A Q ⧸ hAS.cutGradedRadical A Q)) ≃ₐ[K] (Q.Vertex→K) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K)
    (hAS.cutGradedRadicalQuotientAlgEquiv A Q)).trans (scalarProductBaseChangeEquiv k Q.Vertex K)

theorem ASRegular.cutSemisimpleBaseChange_isSemisimple (hAS : A.ASRegular Q)
    (K : Type w) [Field K] [Algebra k K] :
    IsSemisimpleRing (K ⊗[k] (hAS.CutGradedAlgebra A Q ⧸ hAS.cutGradedRadical A Q)) :=
  (hAS.cutSemisimpleBaseChangeEquiv A Q K).symm.toRingEquiv.isSemisimpleRing

end ASGinzburg.ZAlgebra
