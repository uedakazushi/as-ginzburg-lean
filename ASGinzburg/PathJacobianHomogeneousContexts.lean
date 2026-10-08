import ASGinzburg.PathJacobianContexts
import ASGinzburg.PathCutProducts
import ASGinzburg.PathCutUnrollingComparison

/-! Every homogeneous element of the actual Jacobian ideal is a finite
linear combination of relation contexts of that same cut degree. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

def pathJacobianContextDegree (a : Q.Arrow) {u v : Q.Vertex}
    (l : Q.Path u (Q.target a)) (r : Q.Path (Q.source a) v) : ℕ :=
  l.cutDegree+(1-Q.cutDegree a)+r.cutDegree

theorem pathJacobianContext_mem_cut (φ : Q.Potential k) (a : Q.Arrow) {u v : Q.Vertex}
    (l : Q.Path u (Q.target a)) (r : Q.Path (Q.source a) v) :
    Q.pathComp k (Finsupp.single r 1)
      (Q.pathComp k (Q.pathCyclicDerivative k a φ) (Finsupp.single l 1)) ∈
        Q.pathCutComponent k u v (Q.pathJacobianContextDegree a l r:ℤ) := by
  have hl : Finsupp.single l (1:k) ∈ Q.pathCutComponent k u (Q.target a) l.cutDegree :=
    Finsupp.single_mem_supported _ _ rfl
  have hr : Finsupp.single r (1:k) ∈ Q.pathCutComponent k (Q.source a) v r.cutDegree :=
    Finsupp.single_mem_supported _ _ rfl
  simpa only [pathJacobianContextDegree,Nat.cast_add] using
    Q.pathCutComponent_comp k
      (Q.pathCutComponent_comp k hl (Q.pathCyclicDerivative_mem_pathCut k a φ)) hr

def pathJacobianHomogeneousContexts (φ : Q.Potential k) (u v : Q.Vertex) (c : ℤ) :
    Set (Q.PathComponent k u v) :=
  {f | ∃ a : Q.Arrow, ∃ l : Q.Path u (Q.target a), ∃ r : Q.Path (Q.source a) v,
    (Q.pathJacobianContextDegree a l r:ℤ)=c ∧ Q.pathComp k (Finsupp.single r 1)
      (Q.pathComp k (Q.pathCyclicDerivative k a φ) (Finsupp.single l 1))=f}

theorem pathCutProjection_mem_homogeneousContextSpan (φ : Q.Potential k)
    {u v : Q.Vertex} (c : ℤ) {f : Q.PathComponent k u v}
    (hf : f ∈ (Q.pathJacobianIdeal k φ).hom u v) :
    Q.pathCutProjection k u v c f ∈
      Submodule.span k (Q.pathJacobianHomogeneousContexts k φ u v c) := by
  rw [Q.pathJacobianIdeal_eq_contextSpan] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a,l,r,rfl⟩ := hx
    rw [Q.pathCutProjection_on_cut k c _ (Q.pathJacobianContext_mem_cut k φ a l r)]
    split_ifs with h
    · exact Submodule.subset_span ⟨a,l,r,h,rfl⟩
    · exact Submodule.zero_mem _
  | zero => simp
  | add f g hf hg ihf ihg => simpa only [map_add] using Submodule.add_mem _ ihf ihg
  | smul a f hf ih => simpa only [map_smul] using Submodule.smul_mem _ a ih

theorem pathJacobianCut_mem_homogeneousContextSpan (φ : Q.Potential k)
    {u v : Q.Vertex} (c : ℤ) {f : Q.PathComponent k u v}
    (hf : f ∈ (Q.pathJacobianIdeal k φ).hom u v) (hc : f ∈ Q.pathCutComponent k u v c) :
    f ∈ Submodule.span k (Q.pathJacobianHomogeneousContexts k φ u v c) := by
  have h := Q.pathCutProjection_mem_homogeneousContextSpan k φ c hf
  rwa [Q.pathCutProjection_on_cut k c c hc,if_pos rfl] at h

end ASGinzburg.CutQuiver
