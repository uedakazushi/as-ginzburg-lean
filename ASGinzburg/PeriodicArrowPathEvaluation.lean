import ASGinzburg.PeriodIntegerSuccessors
import ASGinzburg.UnrolledPathSheetShift
import ASGinzburg.ArbitraryArrowPathEvaluation

/-! A periodic arrow family evaluates every shifted path through the
actual multiplicative period map. The AS application discharges coherence. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def PeriodIso.liftedStepMap (E : A.PeriodIso Q.vertices)
    (x y : Q.LiftVertex) : A.Hom (Q.height x) (Q.height y) ≃ₗ[k]
      A.Hom (Q.height (Q.shift 1 x)) (Q.height (Q.shift 1 y)) :=
  (E.map (Q.height x) (Q.height y)).trans
    (A.homTransport _ _ _ _ (by rw [Q.height_shift]; ring)
      (by rw [Q.height_shift]; ring))

theorem PeriodIso.liftedStepMap_id (E : A.PeriodIso Q.vertices) (x : Q.LiftVertex) :
    E.liftedStepMap A Q x x (A.id (Q.height x)) = A.id (Q.height (Q.shift 1 x)) := by
  dsimp only [liftedStepMap, LinearEquiv.trans_apply]
  rw [E.map_id, A.homTransport_id]

theorem PeriodIso.liftedStepMap_comp (E : A.PeriodIso Q.vertices)
    {x y z : Q.LiftVertex} (f : A.Hom (Q.height x) (Q.height y))
    (g : A.Hom (Q.height y) (Q.height z)) :
    E.liftedStepMap A Q x z (A.comp g f) =
      A.comp (E.liftedStepMap A Q y z g) (E.liftedStepMap A Q x y f) := by
  dsimp only [liftedStepMap, LinearEquiv.trans_apply]
  rw [E.map_comp, A.homTransport_comp]

def IncomingElementFamily.PeriodCoherent (G : A.IncomingElementFamily Q)
    (E : A.PeriodIso Q.vertices) : Prop :=
  ∀ (w : Q.LiftVertex) (a : Q.incomingArrows w),
    G (Q.shift 1 w) a =
      A.homTransport (Q.height (Q.incomingSource w a)+Q.vertices)
        (Q.height w+Q.vertices)
        (Q.height (Q.incomingSource (Q.shift 1 w) a)) (Q.height (Q.shift 1 w))
        (by simp only [CutQuiver.incomingSource, CutQuiver.liftedSource,
          CutQuiver.height, CutQuiver.shift]; ring)
        (by rw [Q.height_shift]; ring)
        (E.map (Q.height (Q.incomingSource w a)) (Q.height w) (G w a))

theorem arrowPathEvaluation_transport (G : A.IncomingElementFamily Q)
    {x y x' y' : Q.LiftVertex} (hx : x=x') (hy : y=y') (p : Q.UnrolledPath x y) :
    A.arrowPathEvaluation Q G (p.transport hx hy) =
      A.homTransport (Q.height x) (Q.height y) (Q.height x') (Q.height y')
        (congrArg Q.height hx) (congrArg Q.height hy) (A.arrowPathEvaluation Q G p) := by
  subst x'
  subst y'
  rfl

theorem arrowPathEvaluation_shift (G : A.IncomingElementFamily Q)
    (E : A.PeriodIso Q.vertices) (hG : G.PeriodCoherent A Q E)
    {x y : Q.LiftVertex} (p : Q.UnrolledPath x y) :
    A.arrowPathEvaluation Q G (p.shift 1) =
      E.liftedStepMap A Q x y (A.arrowPathEvaluation Q G p) := by
  induction p with
  | nil =>
    simp only [CutQuiver.UnrolledPath.shift, arrowPathEvaluation, E.liftedStepMap_id]
  | @snoc y a p ih =>
    simp only [CutQuiver.UnrolledPath.shift, arrowPathEvaluation,
      arrowPathEvaluation_transport, ih]
    rw [hG y a]
    dsimp only [PeriodIso.liftedStepMap, LinearEquiv.trans_apply]
    rw [A.homTransport_trans, ← A.homTransport_comp, E.map_comp]

end ASGinzburg.ZAlgebra
