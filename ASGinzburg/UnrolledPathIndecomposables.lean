import ASGinzburg.UnrolledPathAlgebra
import ASGinzburg.UnrolledPathFiniteness
import ASGinzburg.ASGeneratorBasis
import Mathlib.LinearAlgebra.Finsupp.Supported

/-! The unrolled path evaluation modulo products kills every path of length
at least two. This supplies the well-definedness direction of (1.9). -/
namespace ASGinzburg.ZAlgebra
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)
variable (R : ∀ w : Q.LiftVertex, A.ASResolution Q w)

noncomputable def unrolledPathIndecomposableMap (u v : Q.LiftVertex) :
    Q.UnrolledPathComponent k u v →ₗ[k]
      (A.Hom (Q.height u) (Q.height v) ⧸
        Submodule.span k (A.products (Q.height u) (Q.height v))) :=
  (Submodule.span k (A.products (Q.height u) (Q.height v))).mkQ.comp
    (A.unrolledPathLinearEvaluation Q R u v)

theorem unrolledPathIndecomposableMap_surjective (u v : Q.LiftVertex) :
    Function.Surjective (A.unrolledPathIndecomposableMap Q R u v) :=
  (Submodule.span k (A.products (Q.height u) (Q.height v))).mkQ_surjective.comp
    (A.unrolledPathLinearEvaluation_surjective Q R u v)

theorem unrolledPathIndecomposableMap_single_long {u v : Q.LiftVertex}
    (p : Q.UnrolledPath u v) (hp : 2 ≤ p.length) :
    A.unrolledPathIndecomposableMap Q R u v (Finsupp.single p 1) = 0 := by
  cases p with
  | nil => simp [CutQuiver.UnrolledPath.length] at hp
  | @snoc v a p =>
    have hp' : 0 < p.length := by
      simp only [CutQuiver.UnrolledPath.length] at hp
      omega
    change (Submodule.span k (A.products (Q.height u) (Q.height v))).mkQ
      (A.unrolledPathLinearEvaluation Q R _ _ (Finsupp.single (.snoc a p) 1)) = 0
    rw [A.unrolledPathLinearEvaluation_single,one_smul]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact Submodule.subset_span ⟨Q.height (Q.incomingSource v a),p.height_lt_of_length_pos hp',
      Q.incomingSource_height_lt v a,A.unrolledPathEvaluation Q R p,(R v).incomingElement a,
      by simp only [unrolledPathEvaluation]⟩

theorem unrolledPathLong_supported_le_ker (u v : Q.LiftVertex) :
    Finsupp.supported k k {p : Q.UnrolledPath u v | 2 ≤ p.length} ≤
      LinearMap.ker (A.unrolledPathIndecomposableMap Q R u v) := by
  rw [Finsupp.supported_eq_span_single]
  apply Submodule.span_le.mpr
  rintro x ⟨p,hp,rfl⟩
  exact A.unrolledPathIndecomposableMap_single_long Q R p hp

end ASGinzburg.ZAlgebra
