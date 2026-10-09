import ASGinzburg.PeriodCutPositiveActionRadical
import ASGinzburg.PeriodCutGradedModuleFunctor
import ASGinzburg.RightModuleMinimality

/-! Genuine minimality means image containment in M rad_gr(R).
The actual cover-to-R functor preserves the paper's minimal differentials. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable {Q : CutQuiver} {E : A.PeriodIso (Q.vertices:ℤ)}

def CutGradedRightModule.IsMinimalMorphism {M N : E.CutGradedRightModule Q} (f : M ⟶ N) : Prop :=
  ∀ v : M.space,f.val v∈N.gradedRadicalActionSpan

variable (Q E)

theorem cornerGradedModuleMap_minimal
    {M N : (E.cornerCoverZAlgebra Q).RightModule} (f : M ⟶ N)
    (hf : (E.cornerCoverZAlgebra Q).IsMinimalMorphism f) :
    CutGradedRightModule.IsMinimalMorphism (E.cornerGradedModuleMap Q f) := by
  intro v
  change E.cornerTotalModuleLinearMap Q f v∈(E.cornerGradedRightModule Q N).gradedRadicalActionSpan
  refine DirectSum.induction_on v ?_ ?_ ?_
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro x w
    change E.cornerTotalModuleLinearMap Q f
      (DirectSum.lof k Q.LiftVertex (E.CornerModuleSpace Q M) x w)∈_
    rw [E.cornerTotalModuleLinearMap_lof]
    exact E.cornerPositiveActionSpan_lof_mem_radical Q N x _ (hf (Q.heightEquiv x) w)
  · intro x y hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy

end ASGinzburg.ZAlgebra.PeriodIso
