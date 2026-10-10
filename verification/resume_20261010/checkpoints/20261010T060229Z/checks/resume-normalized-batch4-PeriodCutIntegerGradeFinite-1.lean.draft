import ASGinzburg.PeriodCutRegularGrading
import ASGinzburg.PeriodCutOppositeHomogeneousSpaces
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! Every actual native integer homogeneous ring component is finite
dimensional, including the zero negative components and the opposite grading. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

 theorem cutIntegerHomogeneousSpace_finite (q : ℤ) :
    Module.Finite k (E.cutIntegerHomogeneousSpace Q q) := by
  by_cases hq : q < 0
  · rw [E.cutIntegerHomogeneousSpace_negative Q hq]
    infer_instance
  · obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hq)
    rw [E.cutIntegerHomogeneousSpace_ofNat]
    change Module.Finite k (LinearMap.range
      (E.cutHomogeneousLinearInclusion (fun i : Q.Vertex => (i.val:ℤ)) n))
    infer_instance

 theorem cutIntegerOppositeHomogeneousSpace_finite (q : ℤ) :
    Module.Finite k (E.cutIntegerOppositeHomogeneousSpace Q q) := by
  letI := E.cutIntegerHomogeneousSpace_finite Q q
  change Module.Finite k ((E.cutIntegerHomogeneousSpace Q q).map
    (MulOpposite.opLinearEquiv k).toLinearMap)
  infer_instance

end ASGinzburg.ZAlgebra.PeriodIso
