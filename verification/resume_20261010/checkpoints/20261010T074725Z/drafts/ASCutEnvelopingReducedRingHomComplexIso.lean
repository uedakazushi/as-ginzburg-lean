import work.ASGinzburgDraft.ASCutEnvelopingReducedRingHomExactness
import work.ASGinzburgDraft.ModuleCatULiftHomology

/-! The actual semisimple reduction of the native enveloping dual is
the actual ordinary right Hom complex, after the canonical field lift. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ModuleCat.Algebra
universe u v
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def ASRegular.cutEnvelopingMinimalReducedRingHomOrdinaryFieldComplexIso
    (hAS : A.ASRegular Q) :
    ((moduleCatULiftFunctor.{u,v,u} k).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (((balancedTensorLeftFunctor k (hAS.CutGradedAlgebra A Q)
        (hAS.CutGradedAlgebra A Q ⧸ hAS.cutGradedRadical A Q)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          (hAS.cutEnvelopingMinimalRingHomRightNatComplex A Q)) ≅
      ordinaryRightRingHomFieldComplex k (hAS.CutGradedAlgebra A Q)
        (envelopingBalancedTensorRegularProjectiveResolution k
          (hAS.CutGradedAlgebra A Q) (hAS.cutSemisimpleRightObject A Q)
          (hAS.cutEnvelopingRegularMinimalResolution A Q)) := by
  let R := hAS.CutGradedAlgebra A Q
  let P := hAS.cutEnvelopingRegularMinimalResolution A Q
  let M := hAS.cutSemisimpleRightObject A Q
  let U := moduleCatULiftFunctor.{u,v,u} k
  letI := hAS.cutSemisimpleRightObject_fieldFinite A Q
  let i₁ := hAS.cutEnvelopingRingDualSemisimpleTensorComplexIso A Q P.complex
  let i₂ := (NatIso.mapHomologicalComplex
    (Functor.isoWhiskerRight (hAS.cutEnvelopingRingDualLeftRawSemisimpleTensorIso A Q) U)
      (ComplexShape.up ℕ)).app P.complex.op
  let i₃ := envelopingFiniteProjectiveRingDualTensorComplexIso k R M P.complex
    (fun n => (ordinaryFiniteProjectiveProperty_iff _ _).mpr
      ⟨hAS.cutEnvelopingRegularMinimalResolution_term_finite A Q n, P.projective n⟩)
  exact (i₁ ≪≫ i₂).symm ≪≫ i₃

end ASGinzburg.ZAlgebra
