import ASGinzburg.PathCutGrading
import ASGinzburg.GinzburgCutCochainComplex
import ASGinzburg.GinzburgJacobianBoundaries

/-! The genuine Jacobian ideal is cut homogeneous. Its degree-c part
is exactly the image of the genuine degree-c negative-one differential. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem pathCutProjection_mem_pathJacobianIdeal (φ : Q.Potential k) {u v : Q.Vertex}
    (c : ℤ) {f : Q.PathComponent k u v} (hf : f ∈ (Q.pathJacobianIdeal k φ).hom u v) :
    Q.pathCutProjection k u v c f ∈ (Q.pathJacobianIdeal k φ).hom u v := by
  rw [←Q.ginzburgBoundarySpace_eq_pathJacobianIdeal k φ u v] at hf ⊢
  obtain ⟨x,hx⟩ := (Q.ginzburgBoundarySpace_mem_iff k φ u v f).mp hf
  apply (Q.ginzburgBoundarySpace_mem_iff k φ u v _).mpr
  refine ⟨⟨Q.ginzburgCutProjection k u v c x.val,
    Q.ginzburgCutProjection_cohomological k c (-1) x.property⟩,?_⟩
  change Q.ginzburgDifferential k φ u v (Q.ginzburgCutProjection k u v c x.val)=_
  rw [Q.ginzburgDifferential_cutProjection,hx,Q.originalGinzburgLinearMap_cutProjection]

noncomputable def pathJacobianCutIdeal (φ : Q.Potential k) (u v : Q.Vertex) (c : ℤ) :
    Submodule k (Q.pathCutComponent k u v c) :=
  ((Q.pathJacobianIdeal k φ).hom u v).comap (Q.pathCutComponent k u v c).subtype

noncomputable def ginzburgCutBoundaryLift (φ : Q.Potential k) (u v : Q.Vertex) (c : ℤ) :
    Q.ginzburgCutCohomologicalComponent k u v (-1) c →ₗ[k] Q.pathCutComponent k u v c :=
  ((Q.ginzburgBoundaryLift k φ u v).comp (Submodule.inclusion
    (show Q.ginzburgCutCohomologicalComponent k u v (-1) c ≤
      Q.ginzburgCohomologicalComponent k u v (-1) from inf_le_left))).codRestrict _ (by
        intro x
        apply (Q.originalGinzburgLinearMap_cut_iff k c _).mp
        change Q.originalGinzburgLinearMap k u v
          (Q.ginzburgBoundaryLift k φ u v ⟨x.val,x.property.1⟩) ∈ _
        rw [Q.originalGinzburgLinearMap_boundaryLift]
        exact Q.ginzburgDifferential_cut k φ c x.property.2)

theorem ginzburgCutBoundaryLift_range (φ : Q.Potential k) (u v : Q.Vertex) (c : ℤ) :
    LinearMap.range (Q.ginzburgCutBoundaryLift k φ u v c)=Q.pathJacobianCutIdeal k φ u v c := by
  apply Submodule.ext
  intro f
  constructor
  · rintro ⟨x,rfl⟩
    change Q.ginzburgBoundaryLift k φ u v ⟨x.val,x.property.1⟩ ∈
      (Q.pathJacobianIdeal k φ).hom u v
    exact Q.ginzburgBoundaryLift_mem_pathJacobianIdeal k φ u v _
  · intro hf
    change f.val ∈ (Q.pathJacobianIdeal k φ).hom u v at hf
    rw [←Q.ginzburgBoundarySpace_eq_pathJacobianIdeal k φ u v] at hf
    obtain ⟨x,hx⟩ := (Q.ginzburgBoundarySpace_mem_iff k φ u v f.val).mp hf
    refine ⟨⟨Q.ginzburgCutProjection k u v c x.val,
      Q.ginzburgCutProjection_cohomological k c (-1) x.property,
      Q.ginzburgCutProjection_mem k c x.val⟩,?_⟩
    apply Subtype.ext
    apply Q.originalGinzburgLinearMap_injective k u v
    change Q.originalGinzburgLinearMap k u v
      (Q.ginzburgBoundaryLift k φ u v ⟨Q.ginzburgCutProjection k u v c x.val,_⟩)=_
    rw [Q.originalGinzburgLinearMap_boundaryLift,Q.ginzburgDifferential_cutProjection,hx,
      Q.ginzburgCutProjection_on_cut k c c (Q.originalGinzburgLinearMap_cut k f.property),
      if_pos rfl]

end ASGinzburg.CutQuiver
