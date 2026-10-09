import ASGinzburg.UnrolledLastArrowCoordinates

/-! The last-arrow coordinates reconstruct actual paths, not just their
dimensions. This will identify the AS first-kernel with genuine path relations. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem unrolledLastArrowLinearEquiv_single (u v : Q.LiftVertex) (huv : u≠v)
    (a : Q.incomingArrows v) (p : Q.UnrolledPath u (Q.incomingSource v a)) (c : k) :
    Q.unrolledLastArrowLinearEquiv k u v huv (Finsupp.single (.snoc a p) c)=
      Pi.single a (Finsupp.single p c) := by
  classical
  ext b q
  rw [Q.unrolledLastArrowLinearEquiv_apply]
  by_cases h : b=a
  · subst b
    simp [Finsupp.single_apply]
  · simp [h]

theorem unrolledLastArrowLinearEquiv_symm_single (u v : Q.LiftVertex) (huv : u≠v)
    (a : Q.incomingArrows v) (x : Q.UnrolledPathComponent k u (Q.incomingSource v a)) :
    (Q.unrolledLastArrowLinearEquiv k u v huv).symm (Pi.single a x)=
      x.mapDomain (UnrolledPath.snoc a) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [Pi.single_add,map_add,Finsupp.mapDomain_add,hx,hy]
  | single p c =>
      rw [Finsupp.mapDomain_single,←Q.unrolledLastArrowLinearEquiv_single k u v huv]
      exact (Q.unrolledLastArrowLinearEquiv k u v huv).symm_apply_apply _

theorem unrolledLastArrow_reconstruction (u v : Q.LiftVertex) (huv : u≠v)
    (f : Q.UnrolledPathComponent k u v) :
    f=∑ a : Q.incomingArrows v,
      (Q.unrolledLastArrowLinearEquiv k u v huv f a).mapDomain (UnrolledPath.snoc a) := by
  classical
  have h := congrArg (Q.unrolledLastArrowLinearEquiv k u v huv).symm
    (Finset.univ_sum_single (Q.unrolledLastArrowLinearEquiv k u v huv f))
  simpa only [map_sum,Q.unrolledLastArrowLinearEquiv_symm_single,
    LinearEquiv.symm_apply_apply] using h.symm

end ASGinzburg.CutQuiver
