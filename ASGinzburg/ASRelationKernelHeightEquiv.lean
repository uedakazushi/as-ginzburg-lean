import ASGinzburg.ASCoverKernelRelationIdeal

/-! Actual lifted path relations and the existing integer-indexed
presentation kernel are linearly equivalent, taking the cover-map
denominator precisely to the genuine IJ submodule. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)
  (R : ∀ w : Q.LiftVertex, A.ASResolution Q w)

noncomputable def pathRelationHeightEquiv (u w : Q.LiftVertex) :
    LinearMap.ker (A.unrolledPathLinearEvaluation Q R u w) ≃ₗ[k]
      (A.unrolledPathPresentation Q R).kernel.hom (Q.height u) (Q.height w) where
  toFun f := ⟨Q.unrolledComponentHeightEquiv k u w f.val,
    (A.unrolledComponentHeightEquiv_mem_presentation_kernel_iff Q R u w f.val).mpr f.property⟩
  invFun f := ⟨(Q.unrolledComponentHeightEquiv k u w).symm f.val,
    (A.unrolledComponentHeightEquiv_mem_presentation_kernel_iff Q R u w _).mp (by
      rw [LinearEquiv.apply_symm_apply]
      exact f.property)⟩
  left_inv f := Subtype.ext ((Q.unrolledComponentHeightEquiv k u w).symm_apply_apply f.val)
  right_inv f := Subtype.ext ((Q.unrolledComponentHeightEquiv k u w).apply_symm_apply f.val)
  map_add' f g := Subtype.ext ((Q.unrolledComponentHeightEquiv k u w).map_add f.val g.val)
  map_smul' c f := Subtype.ext ((Q.unrolledComponentHeightEquiv k u w).map_smul c f.val)

theorem pathRelationHeightEquiv_map_firstKernel_denominator
    (u w : Q.LiftVertex) (huw : u≠w) :
    Submodule.map (A.pathRelationHeightEquiv Q R u w).toLinearMap
      (LinearMap.ker (A.pathRelationsToASFirstKernel Q R u w huw))=
        Submodule.comap ((A.unrolledPathPresentation Q R).kernel.hom
          (Q.height u) (Q.height w)).subtype
          (((A.unrolledPathPresentation Q R).kernel.mul (Q.unrolledArrowIdeal k)).hom
            (Q.height u) (Q.height w)) := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    rw [A.pathRelationsToASFirstKernel_ker,
      A.lastArrowToASFirstTerm_ker_eq_relation_arrow_product] at hx
    exact hx
  · intro hy
    obtain ⟨x,rfl⟩ := (A.pathRelationHeightEquiv Q R u w).surjective y
    apply Submodule.mem_map.mpr
    refine ⟨x,?_,rfl⟩
    rw [A.pathRelationsToASFirstKernel_ker,
      A.lastArrowToASFirstTerm_ker_eq_relation_arrow_product]
    exact hy

end ASGinzburg.ZAlgebra
