import ASGinzburg.ZeroCutJacobianRing
import ASGinzburg.PathJacobianHomogeneousContexts
import ASGinzburg.FiniteComponentDecomposition

/-! Actual cut-zero Jacobian contexts are products of genuine noncut
paths and cut-arrow derivatives in the original finite path ring. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def zeroCutComponentEmbeddingProjection (i j : Q.Vertex) :
    Q.PathComponent k i j →ₗ[k] Q.ZeroCutPathRing k :=
  ((Q.zeroCutPathComponentAlgebra k).totalComponentLinear i j).comp
    ((Q.pathCutProjection k i j 0).codRestrict _ (Q.pathCutProjection_mem k 0))

theorem zeroCutComponentEmbeddingProjection_on_cut (i j : Q.Vertex)
    (f : Q.pathCutComponent k i j 0) :
    Q.zeroCutComponentEmbeddingProjection k i j f.val =
      (Q.zeroCutPathComponentAlgebra k).totalComponent i j f := by
  change (Q.zeroCutPathComponentAlgebra k).totalComponent i j
    ⟨Q.pathCutProjection k i j 0 f.val,_⟩ = _
  apply congrArg
  apply Subtype.ext
  exact (Q.pathCutProjection_on_cut k 0 0 f.property).trans (if_pos rfl)

theorem zeroCutJacobianContext_embedding_mem (φ : Q.Potential k)
    (a : Q.Arrow) {i j : Q.Vertex}
    (l : Q.Path i (Q.target a)) (r : Q.Path (Q.source a) j)
    (hd : (Q.pathJacobianContextDegree a l r : ℤ) = 0) :
    Q.zeroCutComponentEmbeddingProjection k i j
      (Q.pathComp k (Finsupp.single r 1)
        (Q.pathComp k (Q.pathCyclicDerivative k a φ) (Finsupp.single l 1))) ∈
      Q.zeroCutJacobianIdeal k φ := by
  have ha : Q.cut a = true := by
    cases H : Q.cut a
    · simp only [pathJacobianContextDegree,Q.cutDegree_false H,Nat.sub_zero,
        Nat.cast_add,Nat.cast_one] at hd
      omega
    · rfl
  have hl : l.cutDegree = 0 := by
    simp only [pathJacobianContextDegree,Q.cutDegree_true ha,Nat.sub_self,
      Nat.add_zero,Nat.cast_add] at hd
    omega
  have hr : r.cutDegree = 0 := by
    simp only [pathJacobianContextDegree,Q.cutDegree_true ha,Nat.sub_self,
      Nat.add_zero,Nat.cast_add] at hd
    omega
  let B := Q.zeroCutPathComponentAlgebra k
  let L : Q.pathCutComponent k i (Q.target a) 0 :=
    ⟨Finsupp.single l 1,Finsupp.single_mem_supported k 1 (by simp [hl])⟩
  let R : Q.pathCutComponent k (Q.source a) j 0 :=
    ⟨Finsupp.single r 1,Finsupp.single_mem_supported k 1 (by simp [hr])⟩
  let D := Q.zeroCutCyclicDerivative k φ ⟨a,ha⟩
  have hD : B.totalComponent (Q.target a) (Q.source a) D ∈ Q.zeroCutJacobianIdeal k φ :=
    TwoSidedIdeal.subset_span ⟨⟨a,ha⟩,rfl⟩
  have hcontext := (Q.zeroCutJacobianIdeal k φ).mul_mem_left
    (B.totalComponent (Q.source a) j R)
      ((Q.zeroCutJacobianIdeal k φ).mul_mem_right (B.totalComponent i (Q.target a) L) hD)
  rw [B.totalComponent_mul_same,B.totalComponent_mul_same] at hcontext
  have hc : Q.pathComp k (Finsupp.single r 1)
      (Q.pathComp k (Q.pathCyclicDerivative k a φ) (Finsupp.single l 1)) ∈
        Q.pathCutComponent k i j 0 := by
    rw [← hd]
    exact Q.pathJacobianContext_mem_cut k φ a l r
  rw [Q.zeroCutComponentEmbeddingProjection_on_cut k i j ⟨_,hc⟩]
  exact hcontext

theorem zeroCutJacobianComponent_embedding_mem (φ : Q.Potential k) (i j : Q.Vertex)
    (f : Q.pathCutComponent k i j 0)
    (hf : f.val ∈ (Q.pathJacobianIdeal k φ).hom i j) :
    (Q.zeroCutPathComponentAlgebra k).totalComponent i j f ∈ Q.zeroCutJacobianIdeal k φ := by
  have H := Q.pathJacobianCut_mem_homogeneousContextSpan k φ 0 hf f.property
  rw [← Q.zeroCutComponentEmbeddingProjection_on_cut k i j f]
  generalize f.val = x at H ⊢
  induction H using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a,l,r,hd,rfl⟩ := hx
    exact Q.zeroCutJacobianContext_embedding_mem k φ a l r hd
  | zero => simpa only [map_zero] using (Q.zeroCutJacobianIdeal k φ).zero_mem
  | add f g hf hg ihf ihg =>
    simpa only [map_add] using (Q.zeroCutJacobianIdeal k φ).add_mem ihf ihg
  | smul c f hf ih =>
    simpa only [map_smul] using ((Q.zeroCutJacobianIdeal k φ).restrictScalars k).smul_mem c ih

end ASGinzburg.CutQuiver
