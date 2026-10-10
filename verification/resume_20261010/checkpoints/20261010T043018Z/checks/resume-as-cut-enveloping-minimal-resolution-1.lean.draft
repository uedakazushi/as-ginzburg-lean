import work.ASGinzburgDraft.PeriodCutEnvelopingMinimalResolution
import work.ASGinzburgDraft.ASCutEnvelopingRegularGradedData
import work.ASGinzburgDraft.ASCutEnvelopingQuotient

/-! The original AS condition yields the actual minimal projective
resolution of its cut multiplication bimodule over the true enveloping
algebra. Every term has the genuine nonnegative grading and the actual
augmentation-kernel minimality needed for Tor detection. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def ASRegular.cutEnvelopingRegularMinimalResolution (hAS : A.ASRegular Q) :
    ProjectiveResolution (regularEnvelopingModuleCat k (hAS.CutGradedAlgebra A Q)) :=
  (hAS.periodIso A Q).cutEnvelopingRegularMinimalResolution Q

noncomputable def ASRegular.cutEnvelopingRegularMinimalResolutionTermData
    (hAS : A.ASRegular Q) (n : ℕ) :
    GradedOrdinaryModuleData k (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))
      ((hAS.periodIso A Q).cutEnvelopingIntegerHomogeneousSubspace
        (fun i : Q.Vertex => (i.val : ℤ))) :=
  (hAS.periodIso A Q).cutEnvelopingRegularMinimalResolutionTermData Q n

theorem ASRegular.cutEnvelopingRegularMinimalResolutionTermData_ringModule
    (hAS : A.ASRegular Q) (n : ℕ) :
    (hAS.cutEnvelopingRegularMinimalResolutionTermData A Q n).ringModule =
      (hAS.cutEnvelopingRegularMinimalResolution A Q).complex.X n := rfl

theorem ASRegular.cutEnvelopingRegularMinimalResolutionTermData_boundedBelow
    (hAS : A.ASRegular Q) (n : ℕ) :
    (hAS.cutEnvelopingRegularMinimalResolutionTermData A Q n).BoundedBelow 0 :=
  (hAS.periodIso A Q).cutEnvelopingRegularMinimalResolutionTermData_boundedBelow Q n

theorem ASRegular.cutEnvelopingRegularMinimalResolution_minimal
    (hAS : A.ASRegular Q) (i j : ℕ)
    (x : (hAS.cutEnvelopingRegularMinimalResolution A Q).complex.X i) :
    (hAS.cutEnvelopingRegularMinimalResolution A Q).complex.d i j x ∈
      ordinaryIdealActionSpan k (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))
        ((hAS.cutEnvelopingRegularMinimalResolution A Q).complex.X j)
        (hAS.cutEnvelopingAugmentationKernel A Q) :=
  (hAS.periodIso A Q).cutEnvelopingRegularMinimalResolution_minimal Q i j x

end ASGinzburg.ZAlgebra
