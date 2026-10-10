import work.ASGinzburgDraft.PeriodCutOrdinaryRightModuleData
import work.ASGinzburgDraft.PeriodCutOrdinaryCoverData
import work.ASGinzburgDraft.PeriodCutTotalMapSurjectivity
import ASGinzburg.PeriodCutOrdinaryMinimality
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! Every bounded-below ordinary module carrying the native cut grading
has a genuine projective cover with a kernel in the actual radical. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices : ℤ))
local notation "R" => E.CutGradedRing (fun i : Q.Vertex => (Fin.val i : ℤ))

noncomputable def cutGradedJacobsonOppositeIdeal : Ideal Rᵐᵒᵖ :=
  (E.cutGradedJacobson Q).toTwoSided.op.asIdeal

theorem cutGradedJacobsonOppositeIdeal_mem (r : Rᵐᵒᵖ) :
    r ∈ E.cutGradedJacobsonOppositeIdeal Q ↔ r.unop ∈ E.cutGradedJacobson Q := by
  simp only [cutGradedJacobsonOppositeIdeal, TwoSidedIdeal.mem_asIdeal,
    TwoSidedIdeal.mem_op_iff, Ideal.mem_toTwoSided]

noncomputable def cutOrdinaryGradedCoverSource
    (M : GradedOrdinaryModuleData k Rᵐᵒᵖ (E.cutIntegerOppositeHomogeneousSpace Q)) :
    GradedOrdinaryModuleData k Rᵐᵒᵖ (E.cutIntegerOppositeHomogeneousSpace Q) :=
  E.cutRightModuleOrdinaryData Q (E.cornerGradedRightModule Q
    ((E.cornerCoverZAlgebra Q).rightTopBasisFreeModule
      (E.ordinaryGradedDataCutRightModule Q M).recoveredRightModule))

theorem cutOrdinaryGradedCoverSource_boundedBelow
    (M : GradedOrdinaryModuleData k Rᵐᵒᵖ (E.cutIntegerOppositeHomogeneousSpace Q))
    (b : ℤ) (hb : M.BoundedBelow b) :
    (E.cutOrdinaryGradedCoverSource Q M).BoundedBelow b := by
  apply E.cutRightModuleOrdinaryData_boundedBelow Q
  intro q hq
  apply E.cutCornerModule_grade_eq_bot_of_sharp_height_bound Q _ b _ q hq
  exact (E.cornerCoverZAlgebra Q).rightTopBasisFreeModule_isZero_above_of_height_bound
    (E.ordinaryGradedDataCutRightModule Q M).recoveredRightModule
    ((Q.vertices : ℤ) * (-b) + (Q.vertices : ℤ) - 1)
    (E.cutRecoveredRightModule_isZero_above_sharp_lower_bound Q
      (E.ordinaryGradedDataCutRightModule Q M) b hb)

noncomputable def cutOrdinaryGradedCoverπ
    (M : GradedOrdinaryModuleData k Rᵐᵒᵖ (E.cutIntegerOppositeHomogeneousSpace Q)) :
    (E.cutOrdinaryGradedCoverSource Q M).ringModule ⟶ M.ringModule :=
  (E.cutGradedForgetFunctor Q).map
    (E.cornerGradedModuleMap Q ((E.cornerCoverZAlgebra Q).rightTopBasisFreeModuleπ
        (E.ordinaryGradedDataCutRightModule Q M).recoveredRightModule) ≫
      (E.ordinaryGradedDataCutRightModule Q M).recoveredGradedModuleIso.hom) ≫
    (E.ordinaryGradedDataCutRightModuleIso Q M).hom

theorem cutOrdinaryGradedCoverπ_preservesGrade
    (M : GradedOrdinaryModuleData k Rᵐᵒᵖ (E.cutIntegerOppositeHomogeneousSpace Q)) :
    (E.cutOrdinaryGradedCoverSource Q M).PreservesGrade M (E.cutOrdinaryGradedCoverπ Q M) := by
  intro q x hx
  exact (E.ordinaryGradedDataCutRightModule Q M).recoveredGradedModuleIso.hom.property.2 q _
    ((E.cornerGradedModuleMap Q ((E.cornerCoverZAlgebra Q).rightTopBasisFreeModuleπ
      (E.ordinaryGradedDataCutRightModule Q M).recoveredRightModule)).property.2 q x hx)

theorem cutOrdinaryGradedCoverSource_projective
    (M : GradedOrdinaryModuleData k Rᵐᵒᵖ (E.cutIntegerOppositeHomogeneousSpace Q)) :
    Projective (E.cutOrdinaryGradedCoverSource Q M).ringModule := by
  change Projective ((E.cornerModuleRingFunctor Q).obj
    ((E.cornerCoverZAlgebra Q).rightTopBasisFreeModule
      (E.ordinaryGradedDataCutRightModule Q M).recoveredRightModule))
  infer_instance

theorem cutOrdinaryGradedCoverπ_epi
    (M : GradedOrdinaryModuleData k Rᵐᵒᵖ (E.cutIntegerOppositeHomogeneousSpace Q))
    (b : ℤ) (hb : M.BoundedBelow b) : Epi (E.cutOrdinaryGradedCoverπ Q M) := by
  let N := E.ordinaryGradedDataCutRightModule Q M
  let f := (E.cornerCoverZAlgebra Q).rightTopBasisFreeModuleπ N.recoveredRightModule
  have hf : Epi f :=
    (E.cornerCoverZAlgebra Q).rightTopBasisFreeModuleπ_epi N.recoveredRightModule
      ((Q.vertices : ℤ) * (-b) + (Q.vertices : ℤ) - 1)
      (E.cutRecoveredRightModule_isZero_above_sharp_lower_bound Q N b hb)
  have hsurj := E.cornerTotalModuleLinearMap_surjective_of_epi Q f hf
  apply (ModuleCat.epi_iff_surjective (E.cutOrdinaryGradedCoverπ Q M)).mpr
  intro x
  obtain ⟨y, hy⟩ := N.recoveredTotalEquiv.surjective x
  obtain ⟨z, hz⟩ := hsurj y
  refine ⟨z, ?_⟩
  change N.recoveredTotalEquiv (E.cornerTotalModuleLinearMap Q f z) = x
  change E.cornerTotalModuleLinearMap Q f z = y at hz
  rw [hz, hy]

theorem cutOrdinaryGradedCoverπ_kernel_minimal
    (M : GradedOrdinaryModuleData k Rᵐᵒᵖ (E.cutIntegerOppositeHomogeneousSpace Q))
    (x : (E.cutOrdinaryGradedCoverSource Q M).ringModule)
    (hx : E.cutOrdinaryGradedCoverπ Q M x = 0) :
    x ∈ ordinaryIdealActionSpan k Rᵐᵒᵖ
      (E.cutOrdinaryGradedCoverSource Q M).ringModule (E.cutGradedJacobsonOppositeIdeal Q) := by
  let N := E.ordinaryGradedDataCutRightModule Q M
  let C := E.cornerCoverZAlgebra Q
  let f := C.rightTopBasisFreeModuleπ N.recoveredRightModule
  have hx0 : (E.cornerModuleRingFunctor Q).map f x = 0 := by
    change N.recoveredTotalEquiv (E.cornerTotalModuleLinearMap Q f x) = 0 at hx
    have h := N.recoveredTotalEquiv.injective
      (show N.recoveredTotalEquiv (E.cornerTotalModuleLinearMap Q f x) =
        N.recoveredTotalEquiv 0 by simpa only [map_zero] using hx)
    exact h
  let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  have hS : (S.map (E.cornerModuleRingFunctor Q)).Exact :=
    E.cornerModuleRingFunctor_map_exact Q S (ShortComplex.exact_kernel f)
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp hS x hx0
  change (E.cornerModuleRingFunctor Q).map (kernel.ι f) y = x at hy
  have hmin := E.cutGradedMinimalMorphism_ordinary_actionSpan Q
    (E.cornerGradedModuleMap Q (kernel.ι f))
    (E.cornerGradedModuleMap_minimal Q (kernel.ι f)
      (C.rightTopBasisFreeModuleπ_kernel_inclusion_minimal N.recoveredRightModule)) y
  change (E.cornerModuleRingFunctor Q).map (kernel.ι f) y ∈ _ at hmin
  rw [hy] at hmin
  apply Submodule.span_mono _ hmin
  rintro a ⟨r, hr, m, hm⟩
  exact ⟨MulOpposite.op r, (E.cutGradedJacobsonOppositeIdeal_mem Q _).mpr hr, m, hm⟩

noncomputable def cutOrdinaryGradedProjectiveCover
    (b : ℤ) (M : GradedOrdinaryModuleData k Rᵐᵒᵖ (E.cutIntegerOppositeHomogeneousSpace Q))
    (hb : M.BoundedBelow b) :
    GradedOrdinaryProjectiveCover M b (E.cutGradedJacobsonOppositeIdeal Q) where
  source := E.cutOrdinaryGradedCoverSource Q M
  boundedBelow := E.cutOrdinaryGradedCoverSource_boundedBelow Q M b hb
  π := E.cutOrdinaryGradedCoverπ Q M
  preservesGrade := E.cutOrdinaryGradedCoverπ_preservesGrade Q M
  projective := E.cutOrdinaryGradedCoverSource_projective Q M
  epi := E.cutOrdinaryGradedCoverπ_epi Q M b hb
  kernel_minimal := E.cutOrdinaryGradedCoverπ_kernel_minimal Q M

end ASGinzburg.ZAlgebra.PeriodIso
