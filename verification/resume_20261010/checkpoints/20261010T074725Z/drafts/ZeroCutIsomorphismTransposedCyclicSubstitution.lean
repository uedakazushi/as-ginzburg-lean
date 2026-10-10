import work.ASGinzburgDraft.PathSubstitutionCutEulerClosedTrace
import work.ASGinzburgDraft.NoncutFixedPathSubstitution
import work.ASGinzburgDraft.ZeroCutIsomorphismTransposedReplacement

/-! The actual transposed context substitution of ψ equals the actual
potential action of the genuine noncut lift on φ. Invertibility of the
transposed replacement is a separate, subsequently derived step. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem cutArrow_sum_subtype (f : Q.Arrow → CyclicPolynomial k Q.Arrow) :
    (∑ a : Q.Arrow, if Q.cut a = true then f a else 0) =
      ∑ a : {a : Q.Arrow // Q.cut a = true}, f a.val := by
  classical
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) f

variable {φ ψ : Q.Potential k}
variable (F : ZAlgebra.Isomorphism (Q.unrolledJacobianZAlgebra k φ)
  (Q.unrolledJacobianZAlgebra k ψ))

theorem zeroCutIsomorphismPotential_closedTrace :
    ((Q.zeroCutIsomorphismPathAutomorphism k F) • φ).val =
      ∑ a : {a : Q.Arrow // Q.cut a = true}, Q.closedPathTrace k (Q.source a.val)
        (Q.pathComp k (Q.zeroCutIsomorphismDerivativeImage k F a).val
          (Finsupp.single (Q.baseArrowPath a.val) 1)) := by
  classical
  change (VertexCutPathAutomorphism.potentialLinearEquiv Q k
    (Q.zeroCutIsomorphismPathAutomorphism k F) φ).val = _
  rw [VertexCutPathAutomorphism.potential_val_cyclicSubstitution]
  unfold VertexCutPathAutomorphism.wordArrowReplacement
  rw [Q.potential_cut_closedPathTrace_substitution, Q.cutArrow_sum_subtype]
  apply Finset.sum_congr rfl
  intro a _
  rw [Q.zeroCutIsomorphismPathAutomorphism_cut_arrow k F a.val a.property,
    ← VertexCutPathAutomorphism.component_substitution]
  rfl

theorem zeroCutIsomorphismTransposedCyclicSubstitution :
    cyclicSubstitution (fun a => Q.pathWordMap k (Q.source a) (Q.target a)
      (Q.zeroCutIsomorphismTransposedReplacement k F a)) ψ.val =
      ((Q.zeroCutIsomorphismPathAutomorphism k F) • φ).val := by
  classical
  rw [Q.potential_cut_closedPathTrace_substitution]
  have hψ (a : Q.Arrow) (ha : Q.cut a = true) :
      Q.pathArrowSubstitutionComponent k (Q.zeroCutIsomorphismTransposedReplacement k F)
        (Q.target a) (Q.source a) (Q.pathCyclicDerivative k a ψ) =
      Q.pathCyclicDerivative k a ψ := by
    exact Q.pathArrowSubstitutionComponent_eq_self_of_noncut_fixed k _
      (Q.zeroCutIsomorphismTransposedReplacement_noncut k F) _ _
      (Q.zeroCutCyclicDerivative k ψ ⟨a, ha⟩)
  have hsum :
      (∑ a : Q.Arrow, if Q.cut a = true then Q.closedPathTrace k (Q.source a)
        (Q.pathComp k (Q.pathArrowSubstitutionComponent k
          (Q.zeroCutIsomorphismTransposedReplacement k F) (Q.target a) (Q.source a)
            (Q.pathCyclicDerivative k a ψ)) (Q.zeroCutIsomorphismTransposedReplacement k F a)) else 0) =
      ∑ a : Q.Arrow, if Q.cut a = true then Q.closedPathTrace k (Q.source a)
        (Q.pathComp k (Q.pathCyclicDerivative k a ψ)
          (Q.zeroCutIsomorphismTransposedReplacement k F a)) else 0 := by
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : Q.cut a = true
    · rw [if_pos ha, if_pos ha, hψ a ha]
    · rw [if_neg ha, if_neg ha]
  rw [hsum, Q.zeroCutIsomorphismTransposedReplacement_trace,
    Q.zeroCutIsomorphismPotential_closedTrace]

end ASGinzburg.CutQuiver
