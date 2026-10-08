import ASGinzburg.UnrolledPathErasure
import ASGinzburg.UnrolledJacobianRelations

/-! Actual lifted cyclic-derivative relations recover the genuine
original relations under forgetting sheets, with no regularity hypothesis. -/
namespace ASGinzburg.CutQuiver
variable {Q : CutQuiver}

theorem Path.unrollDegree_erase {u v : Q.Vertex} {d : ℕ} (m : ℤ)
    (p : Path.CutDegreePath (Q:=Q) u v d) : (Path.unrollDegree m p).erase=p.val := by
  apply Path.toList_injective
  exact Path.unrollDegree_erase_toList m p

universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem unrolledPathEraseLinearMap_unrollDegree (u v : Q.Vertex) (d : ℕ) (m : ℤ)
    (f : Path.CutDegreePath (Q:=Q) u v d →₀ k) :
    Q.unrolledPathEraseLinearMap k (u,m) (v,m+(d:ℤ))
      (Q.unrollDegreeLinearMap k u v d m f)=
        ((Finsupp.supportedEquivFinsupp (M:=k) (R:=k)
          {p : Q.Path u v | p.cutDegree=d}).symm f).val := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [map_add,hf,hg]
  | single p a =>
    change Q.unrolledPathEraseLinearMap k (u,m) (v,m+(d:ℤ))
      ((Finsupp.single p a).mapDomain (Path.unrollDegree m))=_
    rw [Finsupp.mapDomain_single,unrolledPathEraseLinearMap_single,
      Finsupp.supportedEquivFinsupp_symm_single,Path.unrollDegree_erase]

theorem unrolledJacobianRelation_erase (a : Q.Arrow) (φ : Q.Potential k) (m : ℤ) :
    Q.unrolledPathEraseLinearMap k (Q.target a,m)
      (Q.source a,m+((1-Q.cutDegree a:ℕ):ℤ))
        (Q.unrolledJacobianRelation k a φ m)=Q.pathCyclicDerivative k a φ := by
  unfold unrolledJacobianRelation
  rw [Q.unrolledPathEraseLinearMap_unrollDegree]
  exact congrArg Subtype.val
    ((Finsupp.supportedEquivFinsupp (M:=k) (R:=k)
      {p : Q.Path (Q.target a) (Q.source a) | p.cutDegree=1-Q.cutDegree a}).symm_apply_apply
        ⟨Q.pathCyclicDerivative k a φ,Q.pathCyclicDerivative_fixedCut k a φ⟩)

end ASGinzburg.CutQuiver
