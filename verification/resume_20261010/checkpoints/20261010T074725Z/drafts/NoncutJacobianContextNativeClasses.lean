import work.ASGinzburgDraft.NativeZeroCutDerivativeComparison
import work.ASGinzburgDraft.NoncutJacobianContextCoefficients
import ASGinzburg.FreePathDecomposableProducts

/-! Actual noncut contexts determine actual native minimal-relation
classes. A positive-length path on either side makes the class zero. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def noncutJacobianContextCutValue (φ : Q.Potential k) (i j : Q.Vertex)
    (c : Q.NoncutJacobianContextIndex i j) : Q.pathCutComponent k i j 0 :=
  ⟨Q.noncutJacobianContextValue k φ i j c, by
    have h := Q.pathJacobianContext_mem_cut k φ c.1.val c.2.1.val c.2.2.val
    simpa only [noncutJacobianContextValue, pathJacobianContextDegree,
      c.2.1.property, c.2.2.property, Q.cutDegree_true c.1.property,
      Nat.sub_self, add_zero, Nat.cast_zero] using h⟩

noncomputable def noncutJacobianContextNativeValue (φ : Q.Potential k) (i j : Q.Vertex)
    (c : Q.NoncutJacobianContextIndex i j) :
    (Q.unrolledJacobianIdeal k φ).hom (i.val : ℤ) (j.val : ℤ) :=
  ⟨Q.zeroCutFoundationComponentEquiv k i j (Q.noncutJacobianContextCutValue k φ i j c),
    (Q.zeroCutFoundationComponentEquiv_mem_Jacobian_iff k φ i j
      (Q.noncutJacobianContextCutValue k φ i j c)).mpr
      (Q.pathJacobianContext_mem_ideal k φ i j ⟨c.1.val, c.2.1.val, c.2.2.val, rfl⟩)⟩

noncomputable def noncutJacobianContextMinimalClass (φ : Q.Potential k) (i j : Q.Vertex)
    (c : Q.NoncutJacobianContextIndex i j) :
    Q.MinimalRelationComponent (Q.unrolledJacobianIdeal k φ) (i.val : ℤ) (j.val : ℤ) :=
  Submodule.Quotient.mk (Q.noncutJacobianContextNativeValue k φ i j c)

theorem noncutJacobianContextMinimalClass_zero_of_positive_length (φ : Q.Potential k)
    (i j : Q.Vertex) (c : Q.NoncutJacobianContextIndex i j)
    (hpos : 0 < c.2.1.val.length ∨ 0 < c.2.2.val.length) :
    Q.noncutJacobianContextMinimalClass k φ i j c = 0 := by
  let L : Q.pathCutComponent k i (Q.target c.1.val) 0 :=
    ⟨Finsupp.single c.2.1.val 1, Finsupp.single_mem_supported k 1
      (by change (c.2.1.val.cutDegree : ℤ) = 0; rw [c.2.1.property]; rfl)⟩
  let R : Q.pathCutComponent k (Q.source c.1.val) j 0 :=
    ⟨Finsupp.single c.2.2.val 1, Finsupp.single_mem_supported k 1
      (by change (c.2.2.val.cutDegree : ℤ) = 0; rw [c.2.2.property]; rfl)⟩
  let D := Q.zeroCutCyclicDerivative k φ c.1
  let B := Q.unrolledPathZAlgebra k
  let I := Q.unrolledJacobianIdeal k φ
  let J := Q.unrolledArrowIdeal k
  have hd : Q.zeroCutFoundationComponentEquiv k (Q.target c.1.val) (Q.source c.1.val) D ∈
      I.hom ((Q.target c.1.val).val : ℤ) ((Q.source c.1.val).val : ℤ) :=
    (Q.zeroCutFoundationComponentEquiv_mem_Jacobian_iff k φ _ _ D).mpr
      (Q.pathCyclicDerivative_mem_pathJacobianIdeal k φ c.1.val)
  have hv : (Q.noncutJacobianContextNativeValue k φ i j c).val =
      B.comp (Q.zeroCutFoundationComponentEquiv k (Q.source c.1.val) j R)
        (B.comp (Q.zeroCutFoundationComponentEquiv k (Q.target c.1.val) (Q.source c.1.val) D)
          (Q.zeroCutFoundationComponentEquiv k i (Q.target c.1.val) L)) := by
    change Q.zeroCutFoundationComponentEquiv k i j (Q.zeroCutPathComp k R
      (Q.zeroCutPathComp k D L)) = _
    rw [Q.zeroCutFoundationComponentEquiv_comp, Q.zeroCutFoundationComponentEquiv_comp]
  apply (Q.minimalRelation_mk_eq_zero_iff I (i.val : ℤ) (j.val : ℤ) _).mpr
  rw [hv]
  rcases hpos with hl | hr
  · have hlt := c.2.1.val.zero_cut_increases_vertex hl c.2.1.property
    have hL : Q.zeroCutFoundationComponentEquiv k i (Q.target c.1.val) L ∈
        J.hom (i.val : ℤ) ((Q.target c.1.val).val : ℤ) := by
      rw [Q.unrolledArrowIdeal_off_diagonal_eq_top k _ _ (by exact_mod_cast hlt)]
      exact Submodule.mem_top
    rw [B.comp_assoc]
    apply Submodule.mem_sup_right
    exact J.comp_mem_mul I hL (I.comp_left hd _)
  · have hlt := c.2.2.val.zero_cut_increases_vertex hr c.2.2.property
    have hR : Q.zeroCutFoundationComponentEquiv k (Q.source c.1.val) j R ∈
        J.hom ((Q.source c.1.val).val : ℤ) (j.val : ℤ) := by
      rw [Q.unrolledArrowIdeal_off_diagonal_eq_top k _ _ (by exact_mod_cast hlt)]
      exact Submodule.mem_top
    apply Submodule.mem_sup_left
    exact I.comp_mem_mul J (I.comp_right hd _) hR

end ASGinzburg.CutQuiver
