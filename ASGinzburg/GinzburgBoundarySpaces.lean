import ASGinzburg.GinzburgCochainComplex

/-! Actual degree zero boundaries transported to the ordinary path space. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgBoundaryLift (φ : Q.Potential k) (u v : Q.Vertex) :
    Q.ginzburgCohomologicalComponent k u v (-1) →ₗ[k] Q.PathComponent k u v :=
  (Q.originalGinzburgDegreeZeroEquiv k u v).symm.toLinearMap.comp
    (Q.ginzburgGradedDifferential k φ u v (-1))

noncomputable def ginzburgBoundarySpace (φ : Q.Potential k) (u v : Q.Vertex) :
    Submodule k (Q.PathComponent k u v) := LinearMap.range (Q.ginzburgBoundaryLift k φ u v)

theorem originalGinzburgLinearMap_boundaryLift (φ : Q.Potential k) (u v : Q.Vertex)
    (f : Q.ginzburgCohomologicalComponent k u v (-1)) :
    Q.originalGinzburgLinearMap k u v (Q.ginzburgBoundaryLift k φ u v f)=
      Q.ginzburgDifferential k φ u v f.val := by
  rw [←Q.originalGinzburgDegreeZeroEquiv_coe k]
  change ((Q.originalGinzburgDegreeZeroEquiv k u v)
    ((Q.originalGinzburgDegreeZeroEquiv k u v).symm _)).val=_
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem ginzburgBoundarySpace_mem_iff (φ : Q.Potential k) (u v : Q.Vertex)
    (f : Q.PathComponent k u v) :
    f ∈ Q.ginzburgBoundarySpace k φ u v ↔
      ∃ x : Q.ginzburgCohomologicalComponent k u v (-1),
        Q.ginzburgDifferential k φ u v x.val=Q.originalGinzburgLinearMap k u v f := by
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨x,by rw [←hx,Q.originalGinzburgLinearMap_boundaryLift k φ]⟩
  · rintro ⟨x,hx⟩
    refine ⟨x,?_⟩
    apply Q.originalGinzburgLinearMap_injective k u v
    rw [Q.originalGinzburgLinearMap_boundaryLift k φ,hx]

end ASGinzburg.CutQuiver
