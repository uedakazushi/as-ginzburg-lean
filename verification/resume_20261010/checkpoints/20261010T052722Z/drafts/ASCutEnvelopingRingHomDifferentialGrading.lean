import work.ASGinzburgDraft.ASCutEnvelopingRingHomGrading

/-! The actual differentials of the native minimal enveloping resolution
preserve internal degree. Consequently their genuine ring-Hom dual
cochain differentials preserve the native internal dual grading. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u v
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem ASRegular.cutEnvelopingRegularMinimalResolution_d_preservesGrade
    (hAS : A.ASRegular Q) (n : ℕ) :
    (hAS.cutEnvelopingRegularMinimalResolutionTermData A Q (n + 1)).PreservesGrade
      (hAS.cutEnvelopingRegularMinimalResolutionTermData A Q n)
      ((hAS.cutEnvelopingRegularMinimalResolution A Q).complex.d (n + 1) n) :=
  GradedOrdinaryBoundedModule.resolution_d_preservesGrade
    ((hAS.periodIso A Q).cutEnvelopingGradedCoverSelection Q 0)
    ⟨(hAS.periodIso A Q).cutEnvelopingRegularGradedData Q,
      (hAS.periodIso A Q).cutEnvelopingRegularGradedData_boundedBelow Q⟩ n

theorem ASRegular.cutEnvelopingMinimalRingHomNatComplex_d_preservesGrade
    (hAS : A.ASRegular Q) (n : ℕ) :
    (hAS.cutEnvelopingMinimalRingHomTermData A Q n).PreservesGrade
      (hAS.cutEnvelopingMinimalRingHomTermData A Q (n + 1))
      ((hAS.cutEnvelopingMinimalRingHomNatComplex A Q).d n (n + 1)) := by
  intro q f hf
  exact (hAS.cutEnvelopingRegularMinimalResolutionTermData A Q (n + 1)).ringDualMap_preservesGrade
      (hAS.cutEnvelopingRegularMinimalResolutionTermData A Q n)
      ((hAS.cutEnvelopingRegularMinimalResolution A Q).complex.d (n + 1) n)
      (hAS.cutEnvelopingRegularMinimalResolution_d_preservesGrade A Q n) q f hf

theorem ASRegular.cutEnvelopingMinimalRingHomNatComplex_isZero_ge_four
    (hAS : A.ASRegular Q) (n : ℕ) :
    IsZero ((hAS.cutEnvelopingMinimalRingHomNatComplex A Q).X (n + 4)) :=
  (ordinaryRingDualFunctor (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))).map_isZero
    (hAS.cutEnvelopingRegularMinimalResolution_isZero_ge_four A Q n).op

end ASGinzburg.ZAlgebra
