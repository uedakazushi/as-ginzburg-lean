import work.ASGinzburgDraft.NoncutJacobianContextTransposedFamily
import work.ASGinzburgDraft.ZeroCutIsomorphismDerivativeContexts

/-! The actual noncut lift's finite derivative contexts determine a
genuine cut-homogeneous nonlinear arrow replacement, fixing noncut arrows. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]
variable {φ ψ : Q.Potential k}
variable (F : ZAlgebra.Isomorphism (Q.unrolledJacobianZAlgebra k φ)
  (Q.unrolledJacobianZAlgebra k ψ))

noncomputable def zeroCutIsomorphismTransposedReplacement : Q.PathArrowReplacement k := by
  classical
  exact fun b => if Q.cut b = true then
    ∑ a : {a : Q.Arrow // Q.cut a = true},
      Q.noncutJacobianContextTransposedLinearMap k a b
        (Q.zeroCutIsomorphismDerivativeContextCoefficients k F a)
  else Q.pathIdentityArrowReplacement k b

theorem zeroCutIsomorphismTransposedReplacement_noncut (b : Q.Arrow)
    (hb : Q.cut b = false) :
    Q.zeroCutIsomorphismTransposedReplacement k F b = Q.pathIdentityArrowReplacement k b := by
  simp only [zeroCutIsomorphismTransposedReplacement, hb, Bool.false_eq_true, if_false]

theorem zeroCutIsomorphismTransposedReplacement_mem_cut (b : Q.Arrow) :
    Q.zeroCutIsomorphismTransposedReplacement k F b ∈
      Q.pathCutComponent k (Q.source b) (Q.target b) (Q.cutDegree b : ℤ) := by
  classical
  by_cases hb : Q.cut b = true
  · rw [zeroCutIsomorphismTransposedReplacement, if_pos hb, Q.cutDegree_true hb]
    apply Submodule.sum_mem
    intro a _
    exact Q.noncutJacobianContextTransposedLinearMap_mem_cut k a b _
  · have hc : Q.cut b = false := by
      cases h : Q.cut b
      · rfl
      · exact (hb h).elim
    rw [Q.zeroCutIsomorphismTransposedReplacement_noncut k F b hc, Q.cutDegree_false hc]
    apply Finsupp.single_mem_supported
    change ((Path.snoc (Path.nil (Q.source b)) b rfl).cutDegree : ℤ) = 0
    simp only [Path.cutDegree, Q.cutDegree_false hc, Nat.zero_add, Nat.cast_zero]

theorem zeroCutIsomorphismTransposedReplacement_trace :
    (∑ b : Q.Arrow, if Q.cut b = true then Q.closedPathTrace k (Q.source b)
      (Q.pathComp k (Q.pathCyclicDerivative k b ψ)
        (Q.zeroCutIsomorphismTransposedReplacement k F b)) else 0) =
    ∑ a : {a : Q.Arrow // Q.cut a = true}, Q.closedPathTrace k (Q.source a.val)
      (Q.pathComp k (Q.zeroCutIsomorphismDerivativeImage k F a).val
        (Finsupp.single (Q.baseArrowPath a.val) 1)) := by
  classical
  have hterm (b : Q.Arrow) :
      (if Q.cut b = true then Q.closedPathTrace k (Q.source b)
        (Q.pathComp k (Q.pathCyclicDerivative k b ψ)
          (Q.zeroCutIsomorphismTransposedReplacement k F b)) else 0) =
      ∑ a : {a : Q.Arrow // Q.cut a = true}, Q.closedPathTrace k (Q.source b)
        (Q.pathComp k (Q.pathCyclicDerivative k b ψ)
          (Q.noncutJacobianContextTransposedLinearMap k a b
            (Q.zeroCutIsomorphismDerivativeContextCoefficients k F a))) := by
    by_cases hb : Q.cut b = true
    · simp only [if_pos hb, zeroCutIsomorphismTransposedReplacement, map_sum]
    · have hc : Q.cut b = false := by
        cases h : Q.cut b
        · rfl
        · exact (hb h).elim
      rw [if_neg hb]
      apply Eq.symm
      apply Finset.sum_eq_zero
      intro a _
      simp only [noncutJacobianContextTransposedLinearMap, Finsupp.linearCombination_apply,
        Finsupp.sum, Q.noncutJacobianContextTransposedTerm_noncut k a b hc,
        smul_zero, Finset.sum_const_zero, map_zero]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Q.noncutJacobianContextTransposedLinearMap_trace,
    Q.zeroCutIsomorphismDerivativeContextCoefficients_expansion]

end ASGinzburg.CutQuiver
