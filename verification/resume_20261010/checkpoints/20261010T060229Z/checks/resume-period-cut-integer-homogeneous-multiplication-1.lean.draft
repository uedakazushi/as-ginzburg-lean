import ASGinzburg.PeriodCutRegularRightModule
import work.ASGinzburgDraft.PeriodCutOppositeHomogeneousSpaces

/-! Actual multiplication respects the native integer grading on the
cut ring and its opposite, including all negative integer degrees. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))
local notation "R" => E.CutGradedRing (fun i : Q.Vertex => (Fin.val i:ℤ))

theorem cutIntegerHomogeneousSpace_mul_mem (p q : ℤ) (r : R)
    (hr : r ∈ E.cutIntegerHomogeneousSpace Q p) (s : R)
    (hs : s ∈ E.cutIntegerHomogeneousSpace Q q) :
    r*s ∈ E.cutIntegerHomogeneousSpace Q (p+q) := by
  by_cases hq : q < 0
  · rw [E.cutIntegerHomogeneousSpace_negative Q hq] at hs
    have hz : s = 0 := hs
    rw [hz,mul_zero]
    exact Submodule.zero_mem _
  · obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hq)
    rw [E.cutIntegerHomogeneousSpace_ofNat] at hs
    obtain ⟨a,rfl⟩ := hs
    exact E.cutIntegerHomogeneousSpace_mul_right Q p r hr n a

theorem cutIntegerOppositeHomogeneousSpace_mul_mem (p q : ℤ) (r : Rᵐᵒᵖ)
    (hr : r ∈ E.cutIntegerOppositeHomogeneousSpace Q p) (s : Rᵐᵒᵖ)
    (hs : s ∈ E.cutIntegerOppositeHomogeneousSpace Q q) :
    r*s ∈ E.cutIntegerOppositeHomogeneousSpace Q (p+q) := by
  rw [E.cutIntegerOppositeHomogeneousSpace_mem_iff_unop]
  have h := E.cutIntegerHomogeneousSpace_mul_mem Q q p s.unop
    ((E.cutIntegerOppositeHomogeneousSpace_mem_iff_unop Q q s).mp hs) r.unop
    ((E.cutIntegerOppositeHomogeneousSpace_mem_iff_unop Q p r).mp hr)
  simpa only [MulOpposite.unop_mul,add_comm] using h

end ASGinzburg.ZAlgebra.PeriodIso
