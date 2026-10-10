import ASGinzburg.PeriodCutEnvelopingZeroInclusionGrading
import ASGinzburg.PeriodCutEnvelopingGradedActionSpan
import ASGinzburg.PeriodCutEnvelopingKernelZeroNilpotence
import ASGinzburg.GradedNilpotentFiniteGeneration

/-! Native enveloping graded Nakayama and finite generation, stated on
the actual linear module so that the ordinary category's scalar
dictionary is supplied once at the later specialization. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open scoped DirectSum
set_option linter.unusedSectionVars false
universe u v w
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices : ℤ))
attribute [local instance 2000] cutEnvelopingOppositeFactorScalarTower
  cutEnvelopingOppositeFactorScalarComm cutGradedRingSelfScalarTower cutGradedRingSelfScalarComm
  cutZeroSelfScalarTower cutZeroEnvelopingSelfSMul cutZeroEnvelopingSelfScalarTower
variable (M : Type w) [AddCommGroup M] [Module k M]
  [Module (AlgebraEnvelopingRing k
    (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))) M]
  [IsScalarTower k (AlgebraEnvelopingRing k
    (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))) M]
attribute [local instance 2000] cutEnvelopingZeroRestrictedModule
  cutEnvelopingZeroRestrictedSMul cutEnvelopingZeroRestrictedModuleScalarTower
  cutEnvelopingZeroRestrictedRingModule cutEnvelopingZeroRestrictedRingSMul
  cutEnvelopingZeroRestrictedModuleEnvelopingScalarTower
variable (G : ℤ → Submodule k M) [DirectSum.Decomposition G]
variable (hAct : ∀ p q : ℤ,
  ∀ a ∈ E.cutEnvelopingIntegerHomogeneousSubspace (fun i : Q.Vertex => (i.val : ℤ)) p,
  ∀ x ∈ G q, a • x ∈ G (p+q))

include hAct in
theorem cutEnvelopingLinearGrade_zeroAction_preserves
    (q : ℤ) (a : AlgebraEnvelopingRing k
      (E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) 0))
    (x : M) (hx : x ∈ G q) : a • x ∈ G q := by
  change E.cutEnvelopingZeroInclusion Q a • x ∈ G q
  simpa only [zero_add] using hAct 0 q _
    (E.cutEnvelopingZeroInclusion_mem_integerDegreeZero Q a) x hx

include hAct in
theorem cutEnvelopingLinearGrade_positiveAction_raises
    (t : E.CutEnvelopingPositiveOperator Q) (q : ℤ) (x : M) (hx : x ∈ G q) :
    E.cutEnvelopingPositiveModuleOperator Q M t x ∈
      G (q+(E.cutEnvelopingPositiveOperatorDegree Q t:ℤ)) := by
  change E.cutEnvelopingPositiveOperatorValue Q t • x ∈ _
  have ht : E.cutEnvelopingPositiveOperatorValue Q t ∈
      E.cutEnvelopingIntegerHomogeneousSubspace (fun i : Q.Vertex => (i.val : ℤ))
        (E.cutEnvelopingPositiveOperatorDegree Q t:ℤ) := by
    rw [E.cutEnvelopingIntegerHomogeneousSubspace_natCast]
    exact E.cutEnvelopingPositiveOperatorValue_mem Q t
  simpa only [add_comm] using hAct _ q _ ht x hx

include hAct in
theorem cutEnvelopingLinearGrade_subsingleton_of_radical_top
    (b : ℤ) (hb : ∀ q : ℤ, q < b → G q = ⊥)
    (hRad : ordinaryIdealActionSpan k
      (AlgebraEnvelopingRing k (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ))))
      M (E.cutEnvelopingAugmentationKernel Q) = ⊤) : Subsingleton M := by
  have hTop : gradedNilpotentActionSpan k
      (AlgebraEnvelopingRing k (E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) 0))
      M (E.cutEnvelopingPositiveModuleOperator Q M)
      (E.cutZeroEnvelopingAugmentationKernel Q) = ⊤ := by
    rw [← E.cutEnvelopingAugmentationKernel_moduleActionSpan_eq_gradedNilpotentActionSpan Q M]
    exact hRad
  let result := gradedModule_subsingleton_of_linear_grading_nilpotent_action_span_top k
    (AlgebraEnvelopingRing k (E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) 0))
    M G (E.cutEnvelopingLinearGrade_zeroAction_preserves Q M G hAct)
    (E.cutEnvelopingPositiveOperatorDegree Q) (E.cutEnvelopingPositiveModuleOperator Q M)
    (E.cutZeroEnvelopingAugmentationKernel Q) (2*Q.vertices)
    (E.cutZeroEnvelopingAugmentationKernel_pow_eq_bot Q)
    (E.cutEnvelopingPositiveOperatorDegree_pos Q)
    (E.cutEnvelopingLinearGrade_positiveAction_raises Q M G hAct) b hb hTop
  exact result

include hAct in
theorem cutEnvelopingLinearGrade_finite_of_finite_top
    [FiniteDimensional k (M ⧸ ordinaryIdealActionSpan k
      (AlgebraEnvelopingRing k (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ))))
      M (E.cutEnvelopingAugmentationKernel Q))]
    (b : ℤ) (hb : ∀ q : ℤ, q < b → G q = ⊥) :
    Module.Finite
      (AlgebraEnvelopingRing k (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))) M := by
  letI : FiniteDimensional k (M ⧸ gradedNilpotentActionSpan k
      (AlgebraEnvelopingRing k (E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) 0))
      M (E.cutEnvelopingPositiveModuleOperator Q M) (E.cutZeroEnvelopingAugmentationKernel Q)) := by
    rw [← E.cutEnvelopingAugmentationKernel_moduleActionSpan_eq_gradedNilpotentActionSpan Q M]
    infer_instance
  exact moduleFinite_of_boundedBelow_finite_radical_top k
    (AlgebraEnvelopingRing k (E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) 0))
    (AlgebraEnvelopingRing k (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ))))
    M G (E.cutEnvelopingLinearGrade_zeroAction_preserves Q M G hAct)
    (E.cutEnvelopingPositiveOperatorDegree Q) (E.cutEnvelopingPositiveOperatorValue Q)
    (E.cutEnvelopingPositiveModuleOperator Q M)
    (E.cutEnvelopingPositiveModuleOperator_apply Q M) (E.cutZeroEnvelopingAugmentationKernel Q)
    (2*Q.vertices) (E.cutZeroEnvelopingAugmentationKernel_pow_eq_bot Q)
    (E.cutEnvelopingPositiveOperatorDegree_pos Q)
    (E.cutEnvelopingLinearGrade_positiveAction_raises Q M G hAct) b hb

end ASGinzburg.ZAlgebra.PeriodIso
