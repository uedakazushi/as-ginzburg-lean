import ASGinzburg.PathCyclicDerivativeDegrees
import ASGinzburg.PathDegreeUnrolling
import ASGinzburg.UnrolledPathIdeals

/-! Actual cyclic derivatives lift to homogeneous relations in the genuine
unrolled path algebra, and lie in its arrow-ideal square. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem pathCyclicDerivative_fixedCut (a : Q.Arrow) (φ : Q.Potential k) :
    Q.pathCyclicDerivative k a φ ∈ Finsupp.supported k k
      {p : Q.Path (Q.target a) (Q.source a) | p.cutDegree=1-Q.cutDegree a} := by
  apply Finsupp.supported_mono _ (Q.pathCyclicDerivative_supported_degrees k a φ)
  rintro p ⟨_,hp⟩
  change p.cutDegree=1-Q.cutDegree a
  omega

noncomputable def restrictedJacobianRelation (a : Q.Arrow) (φ : Q.Potential k) :
    (Path.CutDegreePath (Q:=Q) (Q.target a) (Q.source a) (1-Q.cutDegree a) →₀ k) :=
  Finsupp.supportedEquivFinsupp (R:=k) _
    ⟨Q.pathCyclicDerivative k a φ,Q.pathCyclicDerivative_fixedCut k a φ⟩

theorem restrictedJacobianRelation_apply (a : Q.Arrow) (φ : Q.Potential k)
    (p : Path.CutDegreePath (Q:=Q) (Q.target a) (Q.source a) (1-Q.cutDegree a)) :
    Q.restrictedJacobianRelation k a φ p=Q.pathCyclicDerivative k a φ p.val := rfl

theorem restrictedJacobianRelation_supported_long (a : Q.Arrow) (φ : Q.Potential k) :
    Q.restrictedJacobianRelation k a φ ∈ Finsupp.supported k k
      {p : Path.CutDegreePath (Q:=Q) (Q.target a) (Q.source a) (1-Q.cutDegree a) |
        2 ≤ p.val.length} := by
  apply (Finsupp.mem_supported' k _).mpr
  intro p hp
  rw [Q.restrictedJacobianRelation_apply]
  have H : Q.pathCyclicDerivative k a φ ∈ Finsupp.supported k k
      {p : Q.Path (Q.target a) (Q.source a) | 2 ≤ p.length} :=
    Finsupp.supported_mono (fun p hp => hp.1) (Q.pathCyclicDerivative_supported_degrees k a φ)
  exact (Finsupp.mem_supported' k _).mp H p.val hp

noncomputable def unrolledJacobianRelation (a : Q.Arrow) (φ : Q.Potential k) (m : ℤ) :
    Q.UnrolledPathComponent k (Q.target a,m) (Q.source a,m+((1-Q.cutDegree a:ℕ):ℤ)) :=
  Q.unrollDegreeLinearMap k (Q.target a) (Q.source a) (1-Q.cutDegree a) m
    (Q.restrictedJacobianRelation k a φ)

theorem unrolledJacobianRelation_supported_long (a : Q.Arrow) (φ : Q.Potential k) (m : ℤ) :
    Q.unrolledJacobianRelation k a φ m ∈ Q.unrolledPathFiltration k 2
      (Q.target a,m) (Q.source a,m+((1-Q.cutDegree a:ℕ):ℤ)) := by
  have H := Q.restrictedJacobianRelation_supported_long k a φ
  have hm : (Finsupp.supported k k
      {p : Path.CutDegreePath (Q:=Q) (Q.target a) (Q.source a) (1-Q.cutDegree a) |
        2 ≤ p.val.length}).map
      (Q.unrollDegreeLinearMap k (Q.target a) (Q.source a) (1-Q.cutDegree a) m) ≤
        Q.unrolledPathFiltration k 2 (Q.target a,m)
          (Q.source a,m+((1-Q.cutDegree a:ℕ):ℤ)) := by
    rw [unrollDegreeLinearMap,Finsupp.lmapDomain_supported]
    apply Finsupp.supported_mono
    rintro p ⟨q,hq,rfl⟩
    simpa [Path.unrollDegree,Path.unroll_length] using hq
  exact hm ⟨Q.restrictedJacobianRelation k a φ,H,rfl⟩

end ASGinzburg.CutQuiver
