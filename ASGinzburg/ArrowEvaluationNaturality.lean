import ASGinzburg.ArbitraryArrowPathEvaluation
import ASGinzburg.ArbitraryArrowPresentation

/-! Actual free-arrow evaluation is natural under genuine algebra maps,
including the canonical endpoint transports of the Z-algebra presentation. -/
namespace ASGinzburg.ZAlgebra.Homomorphism
universe u v w
variable {k : Type u} [Field k] {B : ZAlgebra.{u,v} k} {A : ZAlgebra.{u,w} k}
  (F : Homomorphism B A) (Q : CutQuiver)

noncomputable def mapIncomingFamily (G : B.IncomingElementFamily Q) :
    A.IncomingElementFamily Q :=
  fun v a => F.map (Q.height (Q.incomingSource v a)) (Q.height v) (G v a)

theorem arrowPathEvaluation_natural (G : B.IncomingElementFamily Q)
    {u v : Q.LiftVertex} (p : Q.UnrolledPath u v) :
    F.map (Q.height u) (Q.height v) (B.arrowPathEvaluation Q G p)=
      A.arrowPathEvaluation Q (F.mapIncomingFamily Q G) p := by
  induction p with
  | nil => simpa only [arrowPathEvaluation] using F.map_id _
  | snoc a p ih => simp only [arrowPathEvaluation,F.map_comp,ih,mapIncomingFamily]

theorem arrowPathLinearEvaluation_natural (G : B.IncomingElementFamily Q)
    (u v : Q.LiftVertex) (f : Q.UnrolledPathComponent k u v) :
    F.map (Q.height u) (Q.height v) (B.arrowPathLinearEvaluation Q G u v f)=
      A.arrowPathLinearEvaluation Q (F.mapIncomingFamily Q G) u v f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [map_add,hf,hg]
  | single p c => simp [F.arrowPathEvaluation_natural]

theorem map_homTransport (i j i' j' : ℤ) (hi : i=i') (hj : j=j') (f : B.Hom i j) :
    F.map i' j' (B.homTransport i j i' j' hi hj f)=
      A.homTransport i j i' j' hi hj (F.map i j f) := by
  subst i'
  subst j'
  rfl

theorem arrowPathPresentation_natural (G : B.IncomingElementFamily Q)
    (i j : ℤ) (f : (Q.unrolledPathZAlgebra k).Hom i j) :
    F.map i j ((B.arrowPathPresentation Q G).map i j f)=
      (A.arrowPathPresentation Q (F.mapIncomingFamily Q G)).map i j f := by
  change Q.UnrolledPathComponent k (Q.heightEquiv.symm i) (Q.heightEquiv.symm j) at f
  change F.map i j (B.homTransport _ _ i j _ _
    (B.arrowPathLinearEvaluation Q G _ _ f))=A.homTransport _ _ i j _ _
      (A.arrowPathLinearEvaluation Q (F.mapIncomingFamily Q G) _ _ f)
  rw [F.map_homTransport,F.arrowPathLinearEvaluation_natural]

end ASGinzburg.ZAlgebra.Homomorphism
