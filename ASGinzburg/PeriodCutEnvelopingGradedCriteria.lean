import ASGinzburg.PeriodCutEnvelopingGradedActions
import ASGinzburg.PeriodCutEnvelopingLinearGradedCriteria

/-! Genuine bounded-below graded enveloping modules satisfy Nakayama,
and a finite-dimensional actual augmentation top gives finite generation.
The radical decomposition and zero-degree nilpotence are proved native
facts, rather than additional hypotheses. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open scoped ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices : ℤ))
variable (M : GradedOrdinaryModuleData k
  (AlgebraEnvelopingRing k (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ))))
  (E.cutEnvelopingIntegerHomogeneousSubspace (fun i : Q.Vertex => (i.val : ℤ))))
attribute [local instance 3000] cutEnvelopingGradedModuleModule
  cutEnvelopingGradedModuleSMul cutEnvelopingGradedModuleScalarTower
  cutEnvelopingGradedModuleFieldModule cutEnvelopingGradedModuleFieldSMul

theorem cutEnvelopingGradedModule_subsingleton_of_radical_top
    (b : ℤ) (hb : M.BoundedBelow b)
    (hRad : ordinaryIdealActionSpan k
      (AlgebraEnvelopingRing k (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ))))
      M.ringModule (E.cutEnvelopingAugmentationKernel Q) = ⊤) :
    Subsingleton M.ringModule := by
  letI := M.decomposition
  let result := E.cutEnvelopingLinearGrade_subsingleton_of_radical_top Q
    M.ringModule M.grade M.smul_mem b hb hRad
  exact result

theorem cutEnvelopingGradedModule_finite_of_finite_top
    [FiniteDimensional k (M.ringModule ⧸ ordinaryIdealActionSpan k
      (AlgebraEnvelopingRing k (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ))))
      M.ringModule (E.cutEnvelopingAugmentationKernel Q))]
    (b : ℤ) (hb : M.BoundedBelow b) :
    Module.Finite
      (AlgebraEnvelopingRing k (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ))))
      M.ringModule := by
  letI := M.decomposition
  let result := E.cutEnvelopingLinearGrade_finite_of_finite_top Q
    M.ringModule M.grade M.smul_mem b hb
  exact result

end ASGinzburg.ZAlgebra.PeriodIso
