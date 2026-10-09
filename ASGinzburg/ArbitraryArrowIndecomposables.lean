import ASGinzburg.ArbitraryArrowPresentation
import ASGinzburg.UnrolledSingleArrows

/-! Arbitrary arrow lifts kill all decomposable path classes. For an
actual arrow-basis system, the one-arrow classes are independent. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)
variable (G : A.IncomingElementFamily Q)

noncomputable def arrowPathIndecomposableMap (u v : Q.LiftVertex) :
    Q.UnrolledPathComponent k u v →ₗ[k]
      (A.Hom (Q.height u) (Q.height v) ⧸
        Submodule.span k (A.products (Q.height u) (Q.height v))) :=
  (Submodule.span k (A.products (Q.height u) (Q.height v))).mkQ.comp
    (A.arrowPathLinearEvaluation Q G u v)

theorem arrowPathIndecomposableMap_single_long {u v : Q.LiftVertex}
    (p : Q.UnrolledPath u v) (hp : 2 ≤ p.length) :
    A.arrowPathIndecomposableMap Q G u v (Finsupp.single p 1) = 0 := by
  cases p with
  | nil => simp [CutQuiver.UnrolledPath.length] at hp
  | @snoc v a p =>
    have hp' : 0 < p.length := by
      simp only [CutQuiver.UnrolledPath.length] at hp
      omega
    change (Submodule.span k (A.products (Q.height u) (Q.height v))).mkQ
      (A.arrowPathLinearEvaluation Q G _ _ (Finsupp.single (.snoc a p) 1)) = 0
    rw [A.arrowPathLinearEvaluation_single,one_smul]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact Submodule.subset_span ⟨Q.height (Q.incomingSource v a),p.height_lt_of_length_pos hp',
      Q.incomingSource_height_lt v a,A.arrowPathEvaluation Q G p,G v a,
      by simp only [arrowPathEvaluation]⟩

theorem arrowPathLong_supported_le_ker (u v : Q.LiftVertex) :
    Finsupp.supported k k {p : Q.UnrolledPath u v | 2 ≤ p.length} ≤
      LinearMap.ker (A.arrowPathIndecomposableMap Q G u v) := by
  rw [Finsupp.supported_eq_span_single]
  apply Submodule.span_le.mpr
  rintro x ⟨p,hp,rfl⟩
  exact A.arrowPathIndecomposableMap_single_long Q G p hp

namespace IncomingBasisSystem
variable {A Q} (B : A.IncomingBasisSystem Q)
open CutQuiver.UnrolledPath

theorem pathIndecomposableMap_singleArrow (u v : Q.LiftVertex)
    (huv : Q.height u<Q.height v) (a : SingleArrowIndex u v) :
    A.arrowPathIndecomposableMap Q B.incomingElement u v (Finsupp.single (singleArrow u v a) 1)=
      B.basis v (Q.height u) huv (singleArrowHeightEquiv u v a) := by
  obtain ⟨a,ha⟩ := a
  subst u
  have h := B.incomingGenerator_class v (Q.height (Q.incomingSource v a)) huv ⟨a,rfl⟩
  simpa [arrowPathIndecomposableMap,arrowPathEvaluation,arrowPathLinearEvaluation,
    incomingGenerator,homTransport,singleArrow,singleArrowHeightEquiv,A.id_comp] using h

theorem path_oneArrow_class_independent (u v : Q.LiftVertex)
    (huv : Q.height u<Q.height v) :
    LinearIndependent k (fun p : {p : Q.UnrolledPath u v // p.length=1} =>
      A.arrowPathIndecomposableMap Q B.incomingElement u v (Finsupp.single p.val 1)) := by
  let e := (singleArrowEquiv u v).symm.trans (singleArrowHeightEquiv u v)
  have heval (p : {p : Q.UnrolledPath u v // p.length=1}) :
      A.arrowPathIndecomposableMap Q B.incomingElement u v (Finsupp.single p.val 1)=
        B.basis v (Q.height u) huv (e p) := by
    have h := B.pathIndecomposableMap_singleArrow u v huv ((singleArrowEquiv u v).symm p)
    have hp : singleArrow u v ((singleArrowEquiv u v).symm p)=p.val :=
      singleArrow_singleArrowOfPath p.val p.property
    rw [hp] at h
    exact h
  simp_rw [heval]
  exact (B.basis v (Q.height u) huv).linearIndependent.comp e e.injective

end IncomingBasisSystem
end ASGinzburg.ZAlgebra
