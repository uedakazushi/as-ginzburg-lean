import ASGinzburg.PeriodCutGradedRightModules
import ASGinzburg.PeriodCornerCover

/-! The actual R representation acts on integer homogeneous corners,
including the zero negative corners, with the correct module degrees. -/
namespace ASGinzburg.ZAlgebra.PeriodIso.CutGradedRightModule
open CategoryTheory
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable {Q : CutQuiver} {E : A.PeriodIso (Q.vertices:ℤ)}

theorem representation_mul_apply (M : E.CutGradedRightModule Q)
    (r s : E.CutGradedRing (fun t : Q.Vertex => (t.val:ℤ))) (v : M.space) :
    (M.representation (r*s)).unop v=(M.representation s).unop ((M.representation r).unop v) := by
  rw [map_mul,MulOpposite.unop_mul]
  rfl

theorem integerCorner_action_mem_grade (M : E.CutGradedRightModule Q)
    (m : ℤ) (i j : Q.Vertex) (r : E.CutGradedRing (fun t : Q.Vertex => (t.val:ℤ)))
    (hr : r∈E.integerCorner Q m i j) (q : ℤ) (v : M.space) (hv : v∈M.grade q) :
    (M.representation r).unop v∈M.grade (q+m) := by
  by_cases hm : 0≤m
  · rw [E.integerCorner_nonneg Q hm] at hr
    rcases hr with ⟨f,rfl⟩
    have h := M.homogeneous m.toNat
      (E.cutMatrixComponent (fun t : Q.Vertex => (t.val:ℤ)) m.toNat i j f) q v hv
    simpa only [cutHomogeneousComponentLinear_apply,Int.toNat_of_nonneg hm] using h
  · rw [E.integerCorner_negative Q (by omega)] at hr
    have hz : r=0 := by simpa only [Submodule.mem_bot] using hr
    rw [hz,map_zero,MulOpposite.unop_zero,LinearMap.zero_apply]
    exact Submodule.zero_mem _

end ASGinzburg.ZAlgebra.PeriodIso.CutGradedRightModule
