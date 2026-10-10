import work.ASGinzburgDraft.PeriodCutEnvelopingMinimalCover
import work.ASGinzburgDraft.GradedOrdinaryResolutionMinimality
import work.ASGinzburgDraft.PeriodCutEnvelopingRegularGradedData

/-! Actual bounded-below cut enveloping modules possess genuine minimal
projective resolutions built from the proved native cover theorem. In
particular this constructs a resolution of the true multiplication
bimodule, without a minimal-resolution existence hypothesis. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory
open scoped DirectSum ModuleCat.Algebra
universe u v
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option quotPrecheck false
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices : ℤ))
attribute [local instance 2000] cutEnvelopingOppositeFactorScalarTower
  cutEnvelopingOppositeFactorScalarComm cutGradedRingSelfScalarTower cutGradedRingSelfScalarComm

local notation "𝓡" => AlgebraEnvelopingRing k
  (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))
local notation "𝓖" => E.cutEnvelopingIntegerHomogeneousSubspace
  (fun i : Q.Vertex => (i.val : ℤ))

noncomputable def cutEnvelopingGradedMinimalResolution
    (b : ℤ) (M : GradedOrdinaryModuleData k 𝓡 𝓖) (hb : M.BoundedBelow b) :
    ProjectiveResolution M.ringModule :=
  GradedOrdinaryBoundedModule.resolution (E.cutEnvelopingGradedCoverSelection Q b) ⟨M,hb⟩

noncomputable def cutEnvelopingGradedMinimalResolutionTermData
    (b : ℤ) (M : GradedOrdinaryModuleData k 𝓡 𝓖) (hb : M.BoundedBelow b) (n : ℕ) :
    GradedOrdinaryModuleData k 𝓡 𝓖 :=
  GradedOrdinaryBoundedModule.termData (E.cutEnvelopingGradedCoverSelection Q b) ⟨M,hb⟩ n

theorem cutEnvelopingGradedMinimalResolutionTermData_ringModule
    (b : ℤ) (M : GradedOrdinaryModuleData k 𝓡 𝓖) (hb : M.BoundedBelow b) (n : ℕ) :
    (E.cutEnvelopingGradedMinimalResolutionTermData Q b M hb n).ringModule =
      (E.cutEnvelopingGradedMinimalResolution Q b M hb).complex.X n := rfl

theorem cutEnvelopingGradedMinimalResolutionTermData_boundedBelow
    (b : ℤ) (M : GradedOrdinaryModuleData k 𝓡 𝓖) (hb : M.BoundedBelow b) (n : ℕ) :
    (E.cutEnvelopingGradedMinimalResolutionTermData Q b M hb n).BoundedBelow b :=
  GradedOrdinaryBoundedModule.term_boundedBelow
    (E.cutEnvelopingGradedCoverSelection Q b) ⟨M,hb⟩ n

theorem cutEnvelopingGradedMinimalResolution_minimal
    (b : ℤ) (M : GradedOrdinaryModuleData k 𝓡 𝓖) (hb : M.BoundedBelow b)
    (i j : ℕ) (x : (E.cutEnvelopingGradedMinimalResolution Q b M hb).complex.X i) :
    (E.cutEnvelopingGradedMinimalResolution Q b M hb).complex.d i j x ∈
      ordinaryIdealActionSpan k 𝓡
        ((E.cutEnvelopingGradedMinimalResolution Q b M hb).complex.X j)
        (E.cutEnvelopingAugmentationKernel Q) :=
  GradedOrdinaryBoundedModule.resolution_d_minimal_all
    (E.cutEnvelopingGradedCoverSelection Q b) ⟨M,hb⟩ i j x

noncomputable def cutEnvelopingRegularMinimalResolution :
    ProjectiveResolution (regularEnvelopingModuleCat k
      (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))) :=
  E.cutEnvelopingGradedMinimalResolution Q 0 (E.cutEnvelopingRegularGradedData Q)
    (E.cutEnvelopingRegularGradedData_boundedBelow Q)

noncomputable def cutEnvelopingRegularMinimalResolutionTermData (n : ℕ) :
    GradedOrdinaryModuleData k 𝓡 𝓖 :=
  E.cutEnvelopingGradedMinimalResolutionTermData Q 0 (E.cutEnvelopingRegularGradedData Q)
    (E.cutEnvelopingRegularGradedData_boundedBelow Q) n

theorem cutEnvelopingRegularMinimalResolutionTermData_ringModule (n : ℕ) :
    (E.cutEnvelopingRegularMinimalResolutionTermData Q n).ringModule =
      (E.cutEnvelopingRegularMinimalResolution Q).complex.X n := rfl

theorem cutEnvelopingRegularMinimalResolutionTermData_boundedBelow (n : ℕ) :
    (E.cutEnvelopingRegularMinimalResolutionTermData Q n).BoundedBelow 0 :=
  E.cutEnvelopingGradedMinimalResolutionTermData_boundedBelow Q 0
    (E.cutEnvelopingRegularGradedData Q) (E.cutEnvelopingRegularGradedData_boundedBelow Q) n

theorem cutEnvelopingRegularMinimalResolution_minimal (i j : ℕ)
    (x : (E.cutEnvelopingRegularMinimalResolution Q).complex.X i) :
    (E.cutEnvelopingRegularMinimalResolution Q).complex.d i j x ∈
      ordinaryIdealActionSpan k 𝓡 ((E.cutEnvelopingRegularMinimalResolution Q).complex.X j)
        (E.cutEnvelopingAugmentationKernel Q) :=
  E.cutEnvelopingGradedMinimalResolution_minimal Q 0 (E.cutEnvelopingRegularGradedData Q)
    (E.cutEnvelopingRegularGradedData_boundedBelow Q) i j x

end ASGinzburg.ZAlgebra.PeriodIso
