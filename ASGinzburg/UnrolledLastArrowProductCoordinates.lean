import ASGinzburg.UnrolledLastArrowProducts

/-! Prefix multiplication in last-arrow coordinates. This is an
actual coefficient equality needed for the AS kernel's right action. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem unrolledLastArrowLinearEquiv_mapDomain_snoc
    (u w : Q.LiftVertex) (huw : u≠w) (a : Q.incomingArrows w)
    (f : Q.UnrolledPathComponent k u (Q.incomingSource w a)) :
    Q.unrolledLastArrowLinearEquiv k u w huw (f.mapDomain (UnrolledPath.snoc a))=
      Pi.single a f := by
  rw [←Q.unrolledLastArrowLinearEquiv_symm_single k u w huw a f,
    LinearEquiv.apply_symm_apply]

theorem unrolledLastArrowLinearEquiv_comp {u v w : Q.LiftVertex}
    (huw : u≠w) (hvw : v≠w)
    (f : Q.UnrolledPathComponent k u v) (g : Q.UnrolledPathComponent k v w)
    (a : Q.incomingArrows w) :
    Q.unrolledLastArrowLinearEquiv k u w huw (Q.unrolledPathComp k g f) a=
      Q.unrolledPathComp k (Q.unrolledLastArrowLinearEquiv k v w hvw g a) f := by
  classical
  have hc : Q.unrolledPathComp k g f=
      ∑ b : Q.incomingArrows w,
        (Q.unrolledPathComp k (Q.unrolledLastArrowLinearEquiv k v w hvw g b) f).mapDomain
          (UnrolledPath.snoc b) := by
    conv_lhs => rw [Q.unrolledLastArrow_reconstruction k v w hvw g]
    simp only [map_sum,LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro b _
    exact Q.unrolledPathComp_mapDomain_snoc k b _ f
  have h := congrArg (Q.unrolledLastArrowLinearEquiv k u w huw) hc
  simp only [map_sum] at h
  simp_rw [Q.unrolledLastArrowLinearEquiv_mapDomain_snoc] at h
  rw [Finset.univ_sum_single] at h
  exact congrFun h a

end ASGinzburg.CutQuiver
