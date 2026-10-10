import work.ASGinzburgDraft.PeriodCutEnvelopingKernelModuleSpan
import work.ASGinzburgDraft.PeriodCutEnvelopingZeroModuleRestriction
import work.ASGinzburgDraft.PeriodCutEnvelopingPositiveModuleOperators
import work.ASGinzburgDraft.PeriodCutZeroEnvelopingNilpotence
import ASGinzburg.GradedNilpotentNakayama

/-! On every actual left enveloping module, the full genuine
augmentation-kernel action span equals the genuine degree-zero nilpotent
and positive-homogeneous operator action span used by graded Nakayama. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v w
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices : ℤ))
attribute [local instance 2000] cutEnvelopingOppositeFactorScalarTower
  cutEnvelopingOppositeFactorScalarComm cutGradedRingSelfScalarTower cutGradedRingSelfScalarComm
variable (M : Type w) [AddCommGroup M] [Module k M]
  [Module (AlgebraEnvelopingRing k
    (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))) M]
  [IsScalarTower k (AlgebraEnvelopingRing k
    (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))) M]

theorem cutEnvelopingAugmentationKernel_moduleActionSpan_eq_gradedNilpotentActionSpan :
    letI := E.cutEnvelopingZeroRestrictedModule Q M
    letI := E.cutEnvelopingZeroRestrictedSMul Q M
    letI := E.cutEnvelopingZeroRestrictedModuleScalarTower Q M
    ordinaryIdealActionSpan k
      (AlgebraEnvelopingRing k (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ))))
      M (E.cutEnvelopingAugmentationKernel Q) =
    gradedNilpotentActionSpan k
      (AlgebraEnvelopingRing k (E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) 0))
      M (E.cutEnvelopingPositiveModuleOperator Q M) (E.cutZeroEnvelopingAugmentationKernel Q) := by
  letI := E.cutEnvelopingZeroRestrictedModule Q M
  letI := E.cutEnvelopingZeroRestrictedSMul Q M
  letI := E.cutEnvelopingZeroRestrictedModuleScalarTower Q M
  rw [E.cutEnvelopingAugmentationKernel_moduleActionSpan_eq_operators Q M]
  apply congrArg (Submodule.span k)
  ext y
  change (∃ r, r ∈ (E.cutEnvelopingZeroKernelOperators Q ∪
      E.cutEnvelopingPositiveHomogeneousOperators Q) ∧ ∃ x : M, r • x = y) ↔
    ((∃ a ∈ E.cutZeroEnvelopingAugmentationKernel Q, ∃ x : M, a • x = y) ∨
      ∃ t : E.CutEnvelopingPositiveOperator Q, ∃ x : M,
        E.cutEnvelopingPositiveModuleOperator Q M t x = y)
  constructor
  · rintro ⟨r,hr,x,hx⟩
    rcases hr with hr | hr
    · obtain ⟨a,ha,rfl⟩ := hr
      exact Or.inl ⟨a,ha,x,hx⟩
    · obtain ⟨t,ht⟩ := (E.mem_cutEnvelopingPositiveHomogeneousOperators_iff Q r).mp hr
      exact Or.inr ⟨t,x,(E.cutEnvelopingPositiveModuleOperator_apply Q M t x).trans
        ((congrArg (fun a => a • x) ht).trans hx)⟩
  · intro hy
    rcases hy with hy | hy
    · obtain ⟨a,ha,x,hx⟩ := hy
      exact ⟨E.cutEnvelopingZeroInclusion Q a,Or.inl ⟨a,ha,rfl⟩,x,hx⟩
    · obtain ⟨t,x,hx⟩ := hy
      exact ⟨E.cutEnvelopingPositiveOperatorValue Q t,
        Or.inr ((E.mem_cutEnvelopingPositiveHomogeneousOperators_iff Q _).mpr ⟨t,rfl⟩),
        x,(E.cutEnvelopingPositiveModuleOperator_apply Q M t x).symm.trans hx⟩

end ASGinzburg.ZAlgebra.PeriodIso
