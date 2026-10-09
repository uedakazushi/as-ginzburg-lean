import ASGinzburg.BasedArrowPathSurjectivity
import ASGinzburg.ArbitraryArrowIndecomposables

/-! The one-arrow quotient classes are independent for the specified
actual family whenever its generator classes are the genuine basis. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)
variable (G : A.IncomingElementFamily Q) (B : A.IncomingBasisSystem Q)
  (hclass : ∀ (w : Q.LiftVertex) (i : ℤ) (hi : i<Q.height w)
    (a : ASResolution.GeneratorIndex (Q:=Q) (w:=w) i),
    (Submodule.span k (A.products i (Q.height w))).mkQ
      (A.incomingElementGenerator Q G w i a)=B.basis w i hi a)
open CutQuiver.UnrolledPath

include hclass in
theorem basedArrowIndecomposableMap_singleArrow (u v : Q.LiftVertex)
    (huv : Q.height u<Q.height v) (a : SingleArrowIndex u v) :
    A.arrowPathIndecomposableMap Q G u v (Finsupp.single (singleArrow u v a) 1)=
      B.basis v (Q.height u) huv (singleArrowHeightEquiv u v a) := by
  obtain ⟨a,ha⟩ := a
  subst u
  have h := hclass v (Q.height (Q.incomingSource v a)) huv ⟨a,rfl⟩
  simpa [arrowPathIndecomposableMap,arrowPathEvaluation,arrowPathLinearEvaluation,
    incomingElementGenerator,homTransport,singleArrow,singleArrowHeightEquiv,A.id_comp] using h

include hclass in
theorem basedArrow_oneArrow_class_independent (u v : Q.LiftVertex)
    (huv : Q.height u<Q.height v) :
    LinearIndependent k (fun p : {p : Q.UnrolledPath u v // p.length=1} =>
      A.arrowPathIndecomposableMap Q G u v (Finsupp.single p.val 1)) := by
  let e := (singleArrowEquiv u v).symm.trans (singleArrowHeightEquiv u v)
  have heval (p : {p : Q.UnrolledPath u v // p.length=1}) :
      A.arrowPathIndecomposableMap Q G u v (Finsupp.single p.val 1)=
        B.basis v (Q.height u) huv (e p) := by
    have h := A.basedArrowIndecomposableMap_singleArrow Q G B hclass u v huv ((singleArrowEquiv u v).symm p)
    have hp : singleArrow u v ((singleArrowEquiv u v).symm p)=p.val :=
      singleArrow_singleArrowOfPath p.val p.property
    rw [hp] at h
    exact h
  simp_rw [heval]
  exact (B.basis v (Q.height u) huv).linearIndependent.comp e e.injective

end ASGinzburg.ZAlgebra
