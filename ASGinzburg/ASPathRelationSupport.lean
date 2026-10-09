import ASGinzburg.UnrolledPathKernelSquare
import ASGinzburg.UnrolledPathFiniteness

/-! Actual AS path relations vanish at and above the target. The
original kernel-square condition is derived from the AS resolution,
so the support statement needs no additional relation hypothesis. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)
  (R : ∀ w : Q.LiftVertex, A.ASResolution Q w)

theorem unrolledPathLinearEvaluation_ker_eq_zero_of_ge (u w : Q.LiftVertex)
    (huw : Q.height w ≤ Q.height u)
    (f : LinearMap.ker (A.unrolledPathLinearEvaluation Q R u w)) : f.val=0 := by
  classical
  have h := A.unrolledPathLinearEvaluation_ker_le_long Q R u w f.property
  ext p
  change f.val p=0
  by_contra hp
  have hlen : 2 ≤ p.length :=
    (Finsupp.mem_supported k f.val).mp h (Finsupp.mem_support_iff.mpr hp)
  have hlt := p.height_lt_of_length_pos (by omega)
  omega

end ASGinzburg.ZAlgebra
