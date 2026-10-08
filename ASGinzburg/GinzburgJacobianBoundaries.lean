import ASGinzburg.PathJacobianIdeal
import ASGinzburg.GinzburgDualContexts

/-! Degree zero boundaries equal the actual generated Jacobian ideal.
No acyclicity or regularity is assumed. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgBoundaryLift_mem_pathJacobianIdeal (φ : Q.Potential k) (u v : Q.Vertex)
    (x : Q.ginzburgCohomologicalComponent k u v (-1)) :
    Q.ginzburgBoundaryLift k φ u v x ∈ (Q.pathJacobianIdeal k φ).hom u v := by
  let S : Set (Q.GinzburgPath u v) := {p | p.cohomologicalDegree=-1}
  let e := Finsupp.supportedEquivFinsupp (M:=k) (R:=k) S
  have hall (y : S →₀ k) :
      Q.ginzburgBoundaryLift k φ u v (e.symm y) ∈ (Q.pathJacobianIdeal k φ).hom u v := by
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
        rw [Finsupp.supportedEquivFinsupp_symm_single]
        rw [←hr]
        exact Q.ginzburgDifferential_dualContext k φ a l r
      rw [hb]
      exact (Q.pathJacobianIdeal k φ).comp_left
        ((Q.pathJacobianIdeal k φ).comp_right (Q.pathCyclicDerivative_mem_pathJacobianIdeal k φ a)
          (Finsupp.single l 1)) (Finsupp.single r 1)
  simpa only [LinearEquiv.symm_apply_apply] using hall (e x)

theorem ginzburgBoundarySpace_le_pathJacobianIdeal (φ : Q.Potential k) (u v : Q.Vertex) :
    Q.ginzburgBoundarySpace k φ u v ≤ (Q.pathJacobianIdeal k φ).hom u v := by
  rintro f ⟨x,rfl⟩
  exact Q.ginzburgBoundaryLift_mem_pathJacobianIdeal k φ u v x

theorem ginzburgBoundarySpace_eq_pathJacobianIdeal (φ : Q.Potential k) (u v : Q.Vertex) :
    Q.ginzburgBoundarySpace k φ u v=(Q.pathJacobianIdeal k φ).hom u v :=
  le_antisymm (Q.ginzburgBoundarySpace_le_pathJacobianIdeal k φ u v)
    (Q.pathJacobianIdeal_le_boundary k φ u v)

end ASGinzburg.CutQuiver
