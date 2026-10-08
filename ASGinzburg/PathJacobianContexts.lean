import ASGinzburg.GinzburgJacobianBoundaries

/-! The genuine Jacobian ideal is spanned by actual cyclic derivatives
with single ordinary paths on both sides. This explicit finite-span
description supports comparison with lifted relation ideals. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

def pathJacobianContexts (φ : Q.Potential k) (u v : Q.Vertex) :
    Set (Q.PathComponent k u v) :=
  {f | ∃ a : Q.Arrow, ∃ l : Q.Path u (Q.target a), ∃ r : Q.Path (Q.source a) v,
    Q.pathComp k (Finsupp.single r 1)
      (Q.pathComp k (Q.pathCyclicDerivative k a φ) (Finsupp.single l 1))=f}

theorem pathJacobianContext_mem_ideal (φ : Q.Potential k) (u v : Q.Vertex) :
    Q.pathJacobianContexts k φ u v ⊆ (Q.pathJacobianIdeal k φ).hom u v := by
  rintro f ⟨a,l,r,rfl⟩
  exact (Q.pathJacobianIdeal k φ).comp_left
    ((Q.pathJacobianIdeal k φ).comp_right (Q.pathCyclicDerivative_mem_pathJacobianIdeal k φ a)
      (Finsupp.single l 1)) (Finsupp.single r 1)

theorem ginzburgBoundaryLift_mem_contextSpan (φ : Q.Potential k) (u v : Q.Vertex)
    (x : Q.ginzburgCohomologicalComponent k u v (-1)) :
    Q.ginzburgBoundaryLift k φ u v x ∈ Submodule.span k (Q.pathJacobianContexts k φ u v) := by
  let S : Set (Q.GinzburgPath u v) := {p | p.cohomologicalDegree=-1}
  let e := Finsupp.supportedEquivFinsupp (M:=k) (R:=k) S
  have hall (y : S →₀ k) : Q.ginzburgBoundaryLift k φ u v (e.symm y) ∈
      Submodule.span k (Q.pathJacobianContexts k φ u v) := by
    classical
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simpa only [map_add] using Submodule.add_mem _ hf hg
    | single p c =>
      have hs : Finsupp.single p c=c • Finsupp.single p (1:k) := by simp
      rw [hs,map_smul,map_smul]
      apply Submodule.smul_mem
      obtain ⟨a,l,r,hr⟩ := p.val.degreeNegOne_decomposition Q p.property
      have hb : Q.ginzburgBoundaryLift k φ u v (e.symm (Finsupp.single p 1))=
          Q.pathComp k (Finsupp.single r 1)
            (Q.pathComp k (Q.pathCyclicDerivative k a φ) (Finsupp.single l 1)) := by
        apply Q.originalGinzburgLinearMap_injective k u v
        rw [Q.originalGinzburgLinearMap_boundaryLift]
        change Q.ginzburgDifferential k φ u v (e.symm (Finsupp.single p 1)).val=_
        rw [Finsupp.supportedEquivFinsupp_symm_single,←hr]
        exact Q.ginzburgDifferential_dualContext k φ a l r
      rw [hb]
      exact Submodule.subset_span ⟨a,l,r,rfl⟩
  simpa only [LinearEquiv.symm_apply_apply] using hall (e x)

theorem pathJacobianIdeal_eq_contextSpan (φ : Q.Potential k) (u v : Q.Vertex) :
    (Q.pathJacobianIdeal k φ).hom u v=Submodule.span k (Q.pathJacobianContexts k φ u v) := by
  apply le_antisymm
  · rw [←Q.ginzburgBoundarySpace_eq_pathJacobianIdeal k φ u v]
    rintro f ⟨x,rfl⟩
    exact Q.ginzburgBoundaryLift_mem_contextSpan k φ u v x
  · exact Submodule.span_le.mpr (Q.pathJacobianContext_mem_ideal k φ u v)

end ASGinzburg.CutQuiver
