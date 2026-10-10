import work.ASGinzburgDraft.AlgebraEnvelopingRingDualTensorEvaluationReducedExactness
import work.ASGinzburgDraft.ASCutOrdinaryRegularExtConcentration
import ASGinzburg.ASCutEnvelopingFiniteResolution
import work.ASGinzburgDraft.ASCutSemisimpleRingDual

/-! The original AS condition alone gives low exactness of the actual
semisimple reduction of the finite enveloping ring-Hom complex. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

 theorem ASRegular.cutSemisimpleRightObject_fieldFinite (hAS : A.ASRegular Q) :
    Module.Finite k (hAS.cutSemisimpleRightObject A Q) := by
  let R := hAS.CutGradedAlgebra A Q
  let J := hAS.cutGradedRadical A Q
  letI : Module.Finite k (R ⧸ J) :=
    Module.Finite.equiv (hAS.cutGradedRadicalQuotientAlgEquiv A Q).symm.toLinearEquiv
  letI : Module.Finite k (R ⧸ J)ᵐᵒᵖ :=
    Module.Finite.equiv (MulOpposite.opLinearEquiv k : (R ⧸ J) ≃ₗ[k] (R ⧸ J)ᵐᵒᵖ)
  exact Module.Finite.equiv (idealQuotientRightCanonicalFieldIso k R J).toLinearEquiv.symm

 theorem ASRegular.cutEnvelopingReducedRingHom_exactAt_low
    (hAS : A.ASRegular Q) (n : ℕ) (hn : n<3) :
    (((envelopingRingDualTensorEvaluationSourceFunctor k (hAS.CutGradedAlgebra A Q)
      (hAS.cutSemisimpleRightObject A Q)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (hAS.cutEnvelopingFiniteProjectiveResolution A Q).complex.op).ExactAt n := by
  let R := hAS.CutGradedAlgebra A Q
  let P := hAS.cutEnvelopingFiniteProjectiveResolution A Q
  letI := hAS.cutSemisimpleRightObject_fieldFinite A Q
  apply envelopingRingDualTensorEvaluationSource_exactAt_low_of_ext_zero k R
    (hAS.cutSemisimpleRightObject A Q) P
  · intro i
    exact (ordinaryFiniteProjectiveProperty_iff _ _).mpr
      ⟨hAS.cutEnvelopingFiniteProjectiveResolution_term_finite A Q i, P.projective i⟩
  · exact hAS.cutEnvelopingFiniteProjectiveResolution_isZero_ge_four A Q 0
  · intro i hi e
    exact hAS.cutSemisimpleRightExt_rightRegular_eq_zero_other A Q i (by omega) e
  · exact hn

end ASGinzburg.ZAlgebra
