import ASGinzburg.FoundationPeriodBasisSystem
import ASGinzburg.ArbitraryArrowPathEvaluation

/-! Actual sheet-wise component maps preserve multiplication and units.
Arrow representatives on all sheets are transported from the zero sheet;
their quotient-basis comparison and one-step coherence remain to be proved. -/
namespace ASGinzburg.CutQuiver
variable (Q : CutQuiver)

theorem height_zeroSheet_period (w : Q.LiftVertex) :
    Q.height (w.1,0)+w.2*Q.vertices=Q.height w := by
  simp only [height,mul_zero,add_zero]
  ring

theorem incomingSource_height_zeroSheet_period (w : Q.LiftVertex) (a : Q.incomingArrows w) :
    Q.height (Q.incomingSource (w.1,0) a)+w.2*Q.vertices=
      Q.height (Q.incomingSource w a) := by
  simp only [incomingSource,liftedSource,height]
  ring

end ASGinzburg.CutQuiver

namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k} (Q : CutQuiver)

theorem homTransport_inverse (i j i' j' : ℤ) (hi : i=i') (hj : j=j') (f : A.Hom i j) :
    A.homTransport i' j' i j hi.symm hj.symm (A.homTransport i j i' j' hi hj f)=f := by
  subst i'
  subst j'
  rfl

theorem PeriodIso.cast_map_transport {p q : ℤ} (h : p=q) (E : A.PeriodIso p)
    (i j i' j' : ℤ) (hi : i+p=i') (hj : j+p=j') (f : A.Hom i j) :
    A.homTransport (i+q) (j+q) i' j'
      ((congrArg (fun t => i+t) h.symm).trans hi)
      ((congrArg (fun t => j+t) h.symm).trans hj)
      ((cast (congrArg (fun t => A.PeriodIso t) h) E).map i j f)=
      A.homTransport (i+p) (j+p) i' j' hi hj (E.map i j f) := by
  subst q
  rfl

theorem PeriodIso.powNat_zero_map {p : ℤ} (E : A.PeriodIso p) (i j : ℤ) (f : A.Hom i j) :
    A.homTransport (i+(0 : ℤ)*p) (j+(0 : ℤ)*p) i j (by ring) (by ring)
      ((E.powNat 0).map i j f)=f := by
  calc
    _=A.homTransport (i+0) (j+0) i j (add_zero i) (add_zero j)
      ((zeroPeriod (A:=A)).map i j f) :=
      PeriodIso.cast_map_transport (zero_mul p).symm (zeroPeriod (A:=A))
        i j i j (add_zero i) (add_zero j) f
    _=f := homTransport_inverse i j (i+0) (j+0) (add_zero i).symm (add_zero j).symm f

noncomputable def PeriodIso.sheetMap (E : A.PeriodIso Q.vertices) (r : ℤ)
    (x y : Q.LiftVertex) :
    A.Hom (Q.height x) (Q.height y) ≃ₗ[k]
      A.Hom (Q.height (Q.shift r x)) (Q.height (Q.shift r y)) :=
  ((E.powInt r).map (Q.height x) (Q.height y)).trans
    (A.homTransport _ _ _ _ (by rw [Q.height_shift];ring) (by rw [Q.height_shift];ring))

theorem PeriodIso.sheetMap_id (E : A.PeriodIso Q.vertices) (r : ℤ) (x : Q.LiftVertex) :
    E.sheetMap Q r x x (A.id (Q.height x))=A.id (Q.height (Q.shift r x)) := by
  dsimp only [sheetMap,LinearEquiv.trans_apply]
  rw [(E.powInt r).map_id,A.homTransport_id]

theorem PeriodIso.sheetMap_comp (E : A.PeriodIso Q.vertices) (r : ℤ)
    (x y z : Q.LiftVertex) (f : A.Hom (Q.height x) (Q.height y))
    (g : A.Hom (Q.height y) (Q.height z)) :
    E.sheetMap Q r x z (A.comp g f)=
      A.comp (E.sheetMap Q r y z g) (E.sheetMap Q r x y f) := by
  dsimp only [sheetMap,LinearEquiv.trans_apply]
  rw [(E.powInt r).map_comp,A.homTransport_comp]

noncomputable def ASRegular.foundationPeriodIncomingElement (A : ZAlgebra.{u,v} k) (Q : CutQuiver)
    (hAS : A.ASRegular Q) : A.IncomingElementFamily Q := fun w a =>
  let w₀ : Q.LiftVertex := (w.1,0)
  let E := hAS.periodIso A Q
  (((E.powInt w.2).map (Q.height (Q.incomingSource w₀ a)) (Q.height w₀)).trans
    (A.homTransport _ _ _ _ (Q.incomingSource_height_zeroSheet_period w a)
      (Q.height_zeroSheet_period w))) ((hAS.resolution A Q w₀).incomingElement a)

theorem ASRegular.foundationPeriodIncomingElement_zero (A : ZAlgebra.{u,v} k) (Q : CutQuiver)
    (hAS : A.ASRegular Q) (j : Q.Vertex) (a : Q.incomingArrows (j,0)) :
    hAS.foundationPeriodIncomingElement A Q (j,0) a=
      (hAS.resolution A Q (j,0)).incomingElement a := by
  dsimp only [foundationPeriodIncomingElement,PeriodIso.powInt,LinearEquiv.trans_apply]
  exact PeriodIso.powNat_zero_map _ _ _ _

end ASGinzburg.ZAlgebra
