import ASGinzburg.PeriodCutEnvelopingRegularGradedData
import ASGinzburg.RegularEnvelopingModuleCatFinite
import ASGinzburg.ASCutGradedDescent

/-! The original AS condition supplies the actual native graded
multiplication bimodule, bounded below and finitely generated over the
actual cut enveloping algebra. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def ASRegular.cutEnvelopingRegularGradedData (hAS : A.ASRegular Q) :
    GradedOrdinaryModuleData k
      (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))
      ((hAS.periodIso A Q).cutEnvelopingIntegerHomogeneousSubspace
        (fun i : Q.Vertex => (i.val : ℤ))) :=
  (hAS.periodIso A Q).cutEnvelopingRegularGradedData Q

theorem ASRegular.cutEnvelopingRegularGradedData_ringModule (hAS : A.ASRegular Q) :
    (hAS.cutEnvelopingRegularGradedData A Q).ringModule =
      regularEnvelopingModuleCat k (hAS.CutGradedAlgebra A Q) := rfl

theorem ASRegular.cutEnvelopingRegularGradedData_grade_mem (hAS : A.ASRegular Q)
    (q : ℤ) (x : (hAS.cutEnvelopingRegularGradedData A Q).ringModule) :
    x ∈ (hAS.cutEnvelopingRegularGradedData A Q).grade q ↔
      x ∈ (hAS.periodIso A Q).cutIntegerHomogeneousSpace Q q := Iff.rfl

theorem ASRegular.cutEnvelopingRegularGradedData_boundedBelow (hAS : A.ASRegular Q) :
    (hAS.cutEnvelopingRegularGradedData A Q).BoundedBelow 0 :=
  (hAS.periodIso A Q).cutEnvelopingRegularGradedData_boundedBelow Q

theorem ASRegular.cutEnvelopingRegularGradedData_finite (hAS : A.ASRegular Q) :
    Module.Finite (AlgebraEnvelopingRing k (hAS.CutGradedAlgebra A Q))
      (hAS.cutEnvelopingRegularGradedData A Q).ringModule :=
  regularEnvelopingModuleCat_finite k (hAS.CutGradedAlgebra A Q)

end ASGinzburg.ZAlgebra
