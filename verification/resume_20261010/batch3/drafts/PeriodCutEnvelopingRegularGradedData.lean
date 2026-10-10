import work.ASGinzburgDraft.RegularEnvelopingNativeGrading
import work.ASGinzburgDraft.GradedOrdinaryModuleData
import work.ASGinzburgDraft.PeriodCutEnvelopingRegularIntegerActions
import ASGinzburg.PeriodCutRegularGrading

/-! Native graded ordinary module data for the actual multiplication
bimodule over the cut enveloping algebra. Its grades have exactly the
original cut-homogeneous carriers and are zero in negative degrees. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory
open scoped DirectSum ModuleCat.Algebra
universe u v
set_option maxHeartbeats 800000
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices : ℤ))

noncomputable def cutEnvelopingRegularGradedData :
    GradedOrdinaryModuleData k
      (AlgebraEnvelopingRing k (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ))))
      (E.cutEnvelopingIntegerHomogeneousSubspace (fun i : Q.Vertex => (i.val : ℤ))) where
  ringModule := regularEnvelopingModuleCat k
    (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))
  grade := regularEnvelopingNativeGrade k _ (E.cutIntegerHomogeneousSpace Q)
  isInternal := regularEnvelopingNativeGrade_isInternal k _ _
    ((E.cutIntegerRegularGradeDecomposition Q).isInternal)
  smul_mem p q a ha x hx := by
    apply (regularEnvelopingNativeGrade_mem k _ _ (p + q) _).2
    exact E.cutEnvelopingRegularModule_integerDegree_smul Q p q a ha x
      ((regularEnvelopingNativeGrade_mem k _ _ q x).1 hx)

theorem cutEnvelopingRegularGradedData_ringModule :
    (E.cutEnvelopingRegularGradedData Q).ringModule =
      regularEnvelopingModuleCat k
        (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ))) := rfl

theorem cutEnvelopingRegularGradedData_grade_mem (q : ℤ)
    (x : (E.cutEnvelopingRegularGradedData Q).ringModule) :
    x ∈ (E.cutEnvelopingRegularGradedData Q).grade q ↔
      x ∈ E.cutIntegerHomogeneousSpace Q q := Iff.rfl

theorem cutEnvelopingRegularGradedData_boundedBelow :
    (E.cutEnvelopingRegularGradedData Q).BoundedBelow 0 := by
  intro q hq
  exact regularEnvelopingNativeGrade_eq_bot k _ _ q
    (E.cutIntegerHomogeneousSpace_negative Q hq)

end ASGinzburg.ZAlgebra.PeriodIso
