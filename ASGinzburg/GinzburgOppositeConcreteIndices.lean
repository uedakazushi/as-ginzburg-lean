import ASGinzburg.GinzburgOppositeDualIndices

/-! The actual family equivalences send each concrete arrow to the
corresponding reversed dual/original generator, preserving the actual incidence. -/
namespace ASGinzburg.CutQuiver
variable (Q : CutQuiver)

theorem ginzburgOriginalOppositeDualEquiv_concrete (v : Q.LiftVertex)
    (a : Q.Arrow) (ha : Q.target a=v.1) :
    Q.ginzburgOriginalOppositeDualEquiv v ⟨.original a,ha,rfl⟩=
      ⟨.dual a,by change (Q.target a).rev=v.1.rev;rw [ha],rfl⟩ := by
  apply Subtype.ext
  exact Q.ginzburgOriginalOppositeDualEquiv_val v ⟨a,ha⟩

theorem ginzburgDualOppositeOriginalEquiv_concrete (v : Q.LiftVertex)
    (a : Q.Arrow) (ha : Q.source a=v.1) :
    Q.ginzburgDualOppositeOriginalEquiv v ⟨.dual a,ha,rfl⟩=
      ⟨.original a,by change (Q.source a).rev=v.1.rev;rw [ha],rfl⟩ := by
  apply Subtype.ext
  exact Q.ginzburgDualOppositeOriginalEquiv_val v ⟨a,ha⟩

end ASGinzburg.CutQuiver
