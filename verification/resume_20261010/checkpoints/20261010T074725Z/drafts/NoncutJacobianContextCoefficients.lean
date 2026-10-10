import ASGinzburg.PathJacobianHomogeneousContexts

/-! Every genuine homogeneous noncut Jacobian relation has a finite
expansion in actual noncut path contexts of actual cut derivatives. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

def NoncutJacobianContextIndex (i j : Q.Vertex) :=
  Σ a : {a : Q.Arrow // Q.cut a = true},
    {l : Q.Path i (Q.target a.val) // l.cutDegree = 0} ×
      {r : Q.Path (Q.source a.val) j // r.cutDegree = 0}

noncomputable def noncutJacobianContextValue (φ : Q.Potential k) (i j : Q.Vertex)
    (c : Q.NoncutJacobianContextIndex i j) : Q.PathComponent k i j :=
  Q.pathComp k (Finsupp.single c.2.2.val 1)
    (Q.pathComp k (Q.pathCyclicDerivative k c.1.val φ) (Finsupp.single c.2.1.val 1))

theorem noncutJacobianContextValue_range (φ : Q.Potential k) (i j : Q.Vertex) :
    Set.range (Q.noncutJacobianContextValue k φ i j) =
      Q.pathJacobianHomogeneousContexts k φ i j 0 := by
  ext f
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨c.1.val, c.2.1.val, c.2.2.val, ?_, rfl⟩
    simp only [pathJacobianContextDegree, c.2.1.property, c.2.2.property,
      Q.cutDegree_true c.1.property, Nat.sub_self, add_zero, Nat.cast_zero]
  · rintro ⟨a, l, r, hd, rfl⟩
    have ha : Q.cut a = true := by
      cases H : Q.cut a
      · simp only [pathJacobianContextDegree, Q.cutDegree_false H, Nat.sub_zero,
          Nat.cast_add, Nat.cast_one] at hd
        omega
      · rfl
    have hl : l.cutDegree = 0 := by
      simp only [pathJacobianContextDegree, Q.cutDegree_true ha, Nat.sub_self,
        Nat.add_zero, Nat.cast_add] at hd
      omega
    have hr : r.cutDegree = 0 := by
      simp only [pathJacobianContextDegree, Q.cutDegree_true ha, Nat.sub_self,
        Nat.add_zero, Nat.cast_add] at hd
      omega
    exact ⟨⟨⟨a, ha⟩, ⟨l, hl⟩, ⟨r, hr⟩⟩, rfl⟩

noncomputable def noncutJacobianContextLinearMap (φ : Q.Potential k) (i j : Q.Vertex) :
    (Q.NoncutJacobianContextIndex i j →₀ k) →ₗ[k] Q.PathComponent k i j :=
  Finsupp.linearCombination k (Q.noncutJacobianContextValue k φ i j)

theorem noncutJacobianContextLinearMap_range (φ : Q.Potential k) (i j : Q.Vertex) :
    LinearMap.range (Q.noncutJacobianContextLinearMap k φ i j) =
      (Q.pathJacobianIdeal k φ).hom i j ⊓ Q.pathCutComponent k i j 0 := by
  rw [noncutJacobianContextLinearMap, Finsupp.range_linearCombination,
    Q.noncutJacobianContextValue_range]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨a, l, r, hd, rfl⟩
    constructor
    · exact Q.pathJacobianContext_mem_ideal k φ i j ⟨a, l, r, rfl⟩
    · rw [← hd]
      exact Q.pathJacobianContext_mem_cut k φ a l r
  · rintro f ⟨hf, hc⟩
    exact Q.pathJacobianCut_mem_homogeneousContextSpan k φ 0 hf hc

noncomputable def noncutJacobianContextCoefficients (φ : Q.Potential k) (i j : Q.Vertex)
    (f : Q.pathCutComponent k i j 0) (hf : f.val ∈ (Q.pathJacobianIdeal k φ).hom i j) :
    Q.NoncutJacobianContextIndex i j →₀ k :=
  Classical.choose (show f.val ∈ LinearMap.range (Q.noncutJacobianContextLinearMap k φ i j)
    from (Q.noncutJacobianContextLinearMap_range k φ i j).symm ▸ ⟨hf, f.property⟩)

theorem noncutJacobianContextCoefficients_expansion (φ : Q.Potential k) (i j : Q.Vertex)
    (f : Q.pathCutComponent k i j 0) (hf : f.val ∈ (Q.pathJacobianIdeal k φ).hom i j) :
    Q.noncutJacobianContextLinearMap k φ i j
      (Q.noncutJacobianContextCoefficients k φ i j f hf) = f.val :=
  Classical.choose_spec (show f.val ∈ LinearMap.range (Q.noncutJacobianContextLinearMap k φ i j)
    from (Q.noncutJacobianContextLinearMap_range k φ i j).symm ▸ ⟨hf, f.property⟩)

end ASGinzburg.CutQuiver
