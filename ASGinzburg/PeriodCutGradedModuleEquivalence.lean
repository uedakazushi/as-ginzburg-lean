import ASGinzburg.PeriodCutRecoveredCounitNaturalIso
import ASGinzburg.PeriodCutRecoveredUnitNaturalIso

/-! The actual cover right modules and ordinary internally graded right R
modules are equivalent. Both functors and comparison isomorphisms are the
component constructions. Mathlib's proved adjointification supplies the
triangle identity from these two genuine natural isomorphisms. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

noncomputable def cornerGradedModuleEquivalence :
    (E.cornerCoverZAlgebra Q).RightModule ≌ E.CutGradedRightModule Q :=
  CategoryTheory.Equivalence.mk (E.cornerGradedModuleFunctor Q)
    CutGradedRightModule.recoveredModuleFunctor (E.cornerRecoveredUnitNaturalIso Q)
    CutGradedRightModule.recoveredCounitNaturalIso

instance cornerGradedModuleEquivalence_functor_linear :
    (E.cornerGradedModuleEquivalence Q).functor.Linear k :=
  inferInstanceAs ((E.cornerGradedModuleFunctor Q).Linear k)

instance cornerGradedModuleEquivalence_inverse_linear :
    (E.cornerGradedModuleEquivalence Q).inverse.Linear k :=
  inferInstanceAs ((CutGradedRightModule.recoveredModuleFunctor (E:=E)).Linear k)

end ASGinzburg.ZAlgebra.PeriodIso
