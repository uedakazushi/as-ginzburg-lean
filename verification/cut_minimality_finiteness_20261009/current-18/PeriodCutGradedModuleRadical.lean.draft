import ASGinzburg.PeriodCutGradedCornerActions
import ASGinzburg.PeriodCutGradedModuleCategory
import ASGinzburg.PeriodCutGradedJacobson

/-! The actual product M rad_gr(R), defined by the genuine R action, is
a k-submodule stable under all R actions and all graded module morphisms. -/
namespace ASGinzburg.ZAlgebra.PeriodIso.CutGradedRightModule
open CategoryTheory
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable {Q : CutQuiver} {E : A.PeriodIso (Q.vertices:ℤ)}

noncomputable def gradedRadicalActionSpan (M : E.CutGradedRightModule Q) : Submodule k M.space :=
  Submodule.span k {y | ∃ r : E.CutGradedRing (fun t : Q.Vertex => (t.val:ℤ)),
    r∈E.cutGradedJacobson Q ∧ ∃ x : M.space,(M.representation r).unop x=y}

theorem gradedRadicalAction_mem (M : E.CutGradedRightModule Q)
    (r : E.CutGradedRing (fun t : Q.Vertex => (t.val:ℤ))) (hr : r∈E.cutGradedJacobson Q)
    (x : M.space) : (M.representation r).unop x∈M.gradedRadicalActionSpan :=
  Submodule.subset_span ⟨r,hr,x,rfl⟩

theorem gradedRadicalActionSpan_action_mem (M : E.CutGradedRightModule Q)
    (s : E.CutGradedRing (fun t : Q.Vertex => (t.val:ℤ))) {v : M.space}
    (hv : v∈M.gradedRadicalActionSpan) :
    (M.representation s).unop v∈M.gradedRadicalActionSpan := by
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨r,hr,x,rfl⟩ := hy
    rw [← M.representation_mul_apply]
    exact M.gradedRadicalAction_mem (r*s) (Ideal.mul_mem_right _ _ hr) x
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
    rw [map_add]
    exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih =>
    rw [map_smul]
    exact Submodule.smul_mem _ c ih

theorem gradedRadicalActionSpan_map_mem {M N : E.CutGradedRightModule Q} (f : M ⟶ N)
    {v : M.space} (hv : v∈M.gradedRadicalActionSpan) : f.val v∈N.gradedRadicalActionSpan := by
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨r,hr,x,rfl⟩ := hy
    rw [f.property.1]
    exact N.gradedRadicalAction_mem r hr (f.val x)
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
    rw [map_add]
    exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih =>
    rw [map_smul]
    exact Submodule.smul_mem _ c ih

end ASGinzburg.ZAlgebra.PeriodIso.CutGradedRightModule
