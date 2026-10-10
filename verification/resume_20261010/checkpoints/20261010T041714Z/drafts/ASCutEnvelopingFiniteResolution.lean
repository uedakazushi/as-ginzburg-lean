import work.ASGinzburgDraft.ASCutEnvelopingMinimalResolution
import work.ASGinzburgDraft.ASCutEnvelopingMinimalTop
import work.ASGinzburgDraft.PeriodCutEnvelopingGradedCriteria
import work.ASGinzburgDraft.FiniteFourTermTruncationOfResolution
import work.ASGinzburgDraft.ASCutUnconditionalDimensionBounds
import ASGinzburg.FourTermProjectiveDimension

/-! The original AS condition gives a genuine finite projective
four-term resolution of the actual multiplication bimodule. Each term's
finite generation follows from its genuine Tor-computed radical top and
bounded-below graded Nakayama; the same detector kills the fourth term.
Consequently its actual enveloping projective dimension is exactly three. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)
attribute [local instance] regularEnvelopingModule regularEnvelopingScalarTower
attribute [local instance 2000] PeriodIso.cutEnvelopingOppositeFactorScalarTower
  PeriodIso.cutEnvelopingOppositeFactorScalarComm PeriodIso.cutGradedRingSelfScalarTower
  PeriodIso.cutGradedRingSelfScalarComm

theorem ASRegular.cutEnvelopingRegularMinimalResolution_term_finite
    (hAS : A.ASRegular Q) (n : ℕ) :
    Module.Finite (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))
      ((hAS.cutEnvelopingRegularMinimalResolution A Q).complex.X n) := by
  let P := hAS.cutEnvelopingRegularMinimalResolution A Q
  let M := hAS.cutEnvelopingRegularMinimalResolutionTermData A Q n
  have hM : M.ringModule=P.complex.X n :=
    hAS.cutEnvelopingRegularMinimalResolutionTermData_ringModule A Q n
  haveI : FiniteDimensional k (M.ringModule ⧸ ordinaryIdealActionSpan k
      (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))
      M.ringModule (hAS.cutEnvelopingAugmentationKernel A Q)) := by
    rw [hM]
    exact hAS.cutEnvelopingMinimalTop_finite A Q P
      (hAS.cutEnvelopingRegularMinimalResolution_minimal A Q) n
  have hFinite := (hAS.periodIso A Q).cutEnvelopingGradedModule_finite_of_finite_top
    Q M 0 (hAS.cutEnvelopingRegularMinimalResolutionTermData_boundedBelow A Q n)
  rw [hM] at hFinite
  exact hFinite

theorem ASRegular.cutEnvelopingRegularMinimalResolution_isZero_ge_four
    (hAS : A.ASRegular Q) (n : ℕ) :
    IsZero ((hAS.cutEnvelopingRegularMinimalResolution A Q).complex.X (n+4)) := by
  let P := hAS.cutEnvelopingRegularMinimalResolution A Q
  let M := hAS.cutEnvelopingRegularMinimalResolutionTermData A Q (n+4)
  have hM : M.ringModule=P.complex.X (n+4) :=
    hAS.cutEnvelopingRegularMinimalResolutionTermData_ringModule A Q (n+4)
  have hRad : ordinaryIdealActionSpan k
      (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))
      M.ringModule (hAS.cutEnvelopingAugmentationKernel A Q)=⊤ := by
    rw [hM]
    exact hAS.cutEnvelopingMinimalActionSpan_eq_top_ge_four A Q P
      (hAS.cutEnvelopingRegularMinimalResolution_minimal A Q) n
  have hZero : Subsingleton M.ringModule :=
    (hAS.periodIso A Q).cutEnvelopingGradedModule_subsingleton_of_radical_top Q M 0
      (hAS.cutEnvelopingRegularMinimalResolutionTermData_boundedBelow A Q (n+4)) hRad
  rw [hM] at hZero
  exact ModuleCat.isZero_iff_subsingleton.mpr hZero

noncomputable def ASRegular.cutEnvelopingFiniteFourTermResolution
    (hAS : A.ASRegular Q) :
    FiniteFourTermProjectiveResolution
      (regularEnvelopingModuleCat k (hAS.CutGradedAlgebra A Q)) :=
  finiteFourTermTruncationOfResolution (hAS.cutEnvelopingRegularMinimalResolution A Q)
    (hAS.cutEnvelopingRegularMinimalResolution_isZero_ge_four A Q 0)
    (hAS.cutEnvelopingRegularMinimalResolution_term_finite A Q 0)
    (hAS.cutEnvelopingRegularMinimalResolution_term_finite A Q 1)
    (hAS.cutEnvelopingRegularMinimalResolution_term_finite A Q 2)
    (hAS.cutEnvelopingRegularMinimalResolution_term_finite A Q 3)

theorem ASRegular.nonempty_cutEnvelopingFiniteFourTermResolution
    (hAS : A.ASRegular Q) :
    Nonempty (FiniteFourTermProjectiveResolution
      (regularEnvelopingModuleCat k (hAS.CutGradedAlgebra A Q))) :=
  ⟨hAS.cutEnvelopingFiniteFourTermResolution A Q⟩

noncomputable def ASRegular.cutEnvelopingFiniteProjectiveResolution
    (hAS : A.ASRegular Q) :
    ProjectiveResolution (regularEnvelopingModuleCat k (hAS.CutGradedAlgebra A Q)) :=
  (hAS.cutEnvelopingFiniteFourTermResolution A Q).toProjectiveResolution

theorem ASRegular.cutEnvelopingFiniteProjectiveResolution_term_finite
    (hAS : A.ASRegular Q) (n : ℕ) :
    Module.Finite (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))
      ((hAS.cutEnvelopingFiniteProjectiveResolution A Q).complex.X n) :=
  (hAS.cutEnvelopingFiniteFourTermResolution A Q).toProjectiveResolution_term_finite n

theorem ASRegular.cutEnvelopingFiniteProjectiveResolution_isZero_ge_four
    (hAS : A.ASRegular Q) (n : ℕ) :
    IsZero ((hAS.cutEnvelopingFiniteProjectiveResolution A Q).complex.X (n+4)) :=
  (hAS.cutEnvelopingFiniteFourTermResolution A Q).toProjectiveResolution_isZero_ge_four n

theorem ASRegular.cutRegularEnveloping_hasProjectiveDimensionLE_three
    (hAS : A.ASRegular Q) :
    HasProjectiveDimensionLE (regularEnvelopingModuleCat k (hAS.CutGradedAlgebra A Q)) 3 :=
  fourTermProjectiveResolution_hasProjectiveDimensionLE
    (hAS.cutEnvelopingRegularMinimalResolution A Q)
    (hAS.cutEnvelopingRegularMinimalResolution_isZero_ge_four A Q 0)

theorem ASRegular.cutRegularEnveloping_projectiveDimension_eq_three
    (hAS : A.ASRegular Q) :
    projectiveDimension (regularEnvelopingModuleCat k (hAS.CutGradedAlgebra A Q))=3 :=
  le_antisymm ((projectiveDimension_le_iff _ 3).mpr
    (hAS.cutRegularEnveloping_hasProjectiveDimensionLE_three A Q))
    (hAS.cutRegularEnveloping_projectiveDimension_ge_three_unconditional A Q)

end ASGinzburg.ZAlgebra
