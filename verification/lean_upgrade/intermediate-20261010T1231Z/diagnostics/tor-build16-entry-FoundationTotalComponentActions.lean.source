import ASGinzburg.FoundationTotalFunctorFaithful
import ASGinzburg.FoundationRingComponentActions

/-! On the actual total module of an existing presheaf, a matrix
component acts by its original A.Hom action followed by a single
component inclusion. Idempotents therefore recover literal projections. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
open scoped ModuleCat.Algebra
attribute [local instance 2000] ModuleCat.isModule
universe u
variable {k : Type u} [Field k] (A : ZAlgebra.{u,u} k) (Q : CutQuiver)

theorem foundationRightTotalAction_component (M : A.FoundationRightModule Q)
    (i j : Q.Vertex) (a : A.Hom (i.val : ℤ) (j.val : ℤ))
    (m : A.foundationRightTotalSpace Q M) :
    A.foundationRightTotalAction Q M ((A.foundationComponents Q).totalComponent i j a) m=
      Pi.single i (A.foundationRightComponentAction Q M a (m j)) := by
  classical
  funext p
  rw [A.foundationRightTotalAction_apply Q M]
  by_cases hp : p=i
  · subst p
    rw [Finset.sum_eq_single j]
    · simp
    · intro q _ hq
      have hz : (A.foundationComponents Q).totalComponent i j a i q=0 := by
        simp [LinearComponentAlgebra.totalComponent,hq]
      rw [hz,A.foundationRightComponentAction_zero Q M i q]
      rfl
    · simp
  · simp only [(A.foundationComponents Q).totalComponent_apply_source_ne i j p _ a hp,
      foundationRightComponentAction_zero,LinearMap.zero_apply,Finset.sum_const_zero,
      Pi.single_eq_of_ne hp]

theorem foundationRingRightProjection_totalModule_apply (M : A.FoundationRightModule Q)
    (i : Q.Vertex) (m : A.foundationRightTotalModule Q M) :
    A.foundationRingRightProjection Q (A.foundationRightTotalModule Q M) i m=Pi.single i (m i) := by
  change A.foundationRightTotalAction Q M ((A.foundationComponents Q).totalComponent i i
    (A.id (i.val : ℤ))) m=_
  rw [A.foundationRightTotalAction_component Q M i i,A.foundationRightComponentAction_id Q M i]
  rfl

end ASGinzburg.ZAlgebra
