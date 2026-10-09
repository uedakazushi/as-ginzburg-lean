import ASGinzburg.PeriodIntegerSuccessors

/-! The concrete AS foundation arrow representatives are coherent on
all adjacent integer sheets. The period is derived from ASRegular. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem ASRegular.foundationPeriodIncomingElement_int_succ (hAS : A.ASRegular Q)
    (m : ℤ) (j : Q.Vertex) (a : Q.incomingArrows (j,0)) :
    hAS.foundationPeriodIncomingElement A Q (j,m+1) a =
      A.homTransport
        (Q.height (Q.incomingSource (j,m) a)+Q.vertices)
        (Q.height (j,m)+Q.vertices)
        (Q.height (Q.incomingSource (j,m+1) a))
        (Q.height (j,m+1))
        (by simp only [CutQuiver.incomingSource, CutQuiver.liftedSource, CutQuiver.height]; ring)
        (by simp only [CutQuiver.height]; ring)
        ((hAS.periodIso A Q).map (Q.height (Q.incomingSource (j,m) a))
          (Q.height (j,m))
          (hAS.foundationPeriodIncomingElement A Q (j,m) a)) := by
  dsimp only [foundationPeriodIncomingElement, LinearEquiv.trans_apply]
  rw [PeriodIso.powInt_succ_apply, PeriodIso.map_homTransport,
    A.homTransport_trans, A.homTransport_trans]

end ASGinzburg.ZAlgebra
