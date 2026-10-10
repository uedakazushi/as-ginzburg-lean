import ASGinzburg.ASResolution

/-! Every target index on the nonzero lower terms of an AS resolution
is strictly below the index of its representable in degree zero. -/

namespace ASGinzburg.CutQuiver
variable (Q : CutQuiver)

theorem asSecondSource_height_lt (w : Q.LiftVertex)
    (a : Q.outgoingArrows (Q.tau.symm w)) :
    Q.height (Q.outgoingTarget (Q.tau.symm w) a) < Q.height w := by
  have hd := Q.lifted_height_difference a.val (Q.tau.symm w).2
  rw [Q.outgoing_liftedSource] at hd
  change Q.height (Q.outgoingTarget (Q.tau.symm w) a) -
    Q.height (Q.tau.symm w) = Q.winding a.val at hd
  have ht := Q.height_tau (Q.tau.symm w)
  simp only [Equiv.apply_symm_apply] at ht
  have hw := Q.winding_lt_period a.val
  omega

theorem asTopSource_height_lt (w : Q.LiftVertex) :
    Q.height (Q.tau.symm w) < Q.height w := by
  have ht := Q.height_tau (Q.tau.symm w)
  simp only [Equiv.apply_symm_apply] at ht
  have hn := Q.at_least_three
  omega

end ASGinzburg.CutQuiver
