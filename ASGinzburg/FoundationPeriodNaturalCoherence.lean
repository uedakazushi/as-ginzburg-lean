import ASGinzburg.PeriodIterationFormulas

/-! The concrete foundation arrow representatives on adjacent
nonnegative sheets are related by the AS-derived period itself.
Negative-sheet coherence is a separate remaining obligation. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem ASRegular.foundationPeriodIncomingElement_nat_succ (hAS : A.ASRegular Q)
    (n : ℕ) (j : Q.Vertex) (a : Q.incomingArrows (j,0)) :
    hAS.foundationPeriodIncomingElement A Q (j,((n+1 : ℕ) : ℤ)) a=
      A.homTransport
        (Q.height (Q.incomingSource (j,(n : ℤ)) a)+Q.vertices)
        (Q.height (j,(n : ℤ))+Q.vertices)
        (Q.height (Q.incomingSource (j,((n+1 : ℕ) : ℤ)) a))
        (Q.height (j,((n+1 : ℕ) : ℤ)))
        (by simp only [CutQuiver.incomingSource,CutQuiver.liftedSource,CutQuiver.height];push_cast;ring)
        (by simp only [CutQuiver.height];push_cast;ring)
        ((hAS.periodIso A Q).map (Q.height (Q.incomingSource (j,(n : ℤ)) a))
          (Q.height (j,(n : ℤ)))
          (hAS.foundationPeriodIncomingElement A Q (j,(n : ℤ)) a)) := by
  dsimp only [foundationPeriodIncomingElement,LinearEquiv.trans_apply,PeriodIso.powInt]
  rw [PeriodIso.powNat_succ_apply,PeriodIso.map_homTransport,
    A.homTransport_trans,A.homTransport_trans]

end ASGinzburg.ZAlgebra
