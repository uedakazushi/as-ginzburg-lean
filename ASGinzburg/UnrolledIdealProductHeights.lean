import ASGinzburg.UnrolledJacobianLiftIdeal

/-! Genuine products of arbitrary integer-indexed free-path ideals
are exactly the height images of actual lifted products. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

def unrolledIdealProductLift (I J : (Q.unrolledPathZAlgebra k).LinearIdeal)
    (u w : Q.LiftVertex) : Submodule k (Q.UnrolledPathComponent k u w) :=
  Submodule.span k {x | ∃ v : Q.LiftVertex,
    ∃ f : Q.UnrolledPathComponent k u v,
      Q.unrolledComponentHeightEquiv k u v f∈I.hom (Q.height u) (Q.height v) ∧
      ∃ g : Q.UnrolledPathComponent k v w,
        Q.unrolledComponentHeightEquiv k v w g∈J.hom (Q.height v) (Q.height w) ∧
          Q.unrolledPathComp k g f=x}

theorem unrolledIdealProductLift_map_height (I J : (Q.unrolledPathZAlgebra k).LinearIdeal)
    (u w : Q.LiftVertex) :
    Submodule.map (Q.unrolledComponentHeightEquiv k u w).toLinearMap
      (Q.unrolledIdealProductLift k I J u w)=(I.mul J).hom (Q.height u) (Q.height w) := by
  apply le_antisymm
  · rw [unrolledIdealProductLift,Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro x ⟨y,⟨v,f,hf,g,hg,rfl⟩,rfl⟩
    change Q.unrolledComponentHeightEquiv k u w (Q.unrolledPathComp k g f)∈_
    rw [Q.unrolledComponentHeightEquiv_comp]
    exact I.comp_mem_mul J hf hg
  · apply Submodule.span_le.mpr
    rintro x ⟨l,f,hf,g,hg,rfl⟩
    obtain ⟨v,rfl⟩ := Q.height_bijective.surjective l
    obtain ⟨p,rfl⟩ := (Q.unrolledComponentHeightEquiv k u v).surjective f
    obtain ⟨q,rfl⟩ := (Q.unrolledComponentHeightEquiv k v w).surjective g
    apply Submodule.mem_map.mpr
    exact ⟨Q.unrolledPathComp k q p,Submodule.subset_span ⟨v,p,hf,q,hg,rfl⟩,
      Q.unrolledComponentHeightEquiv_comp k p q⟩

theorem unrolledIdealProductLift_eq_comap (I J : (Q.unrolledPathZAlgebra k).LinearIdeal)
    (u w : Q.LiftVertex) :
    Q.unrolledIdealProductLift k I J u w=
      Submodule.comap (Q.unrolledComponentHeightEquiv k u w).toLinearMap
        ((I.mul J).hom (Q.height u) (Q.height w)) := by
  rw [←Q.unrolledIdealProductLift_map_height k I J u w]
  exact (Submodule.comap_map_eq_of_injective
    (f := (Q.unrolledComponentHeightEquiv k u w).toLinearMap)
    (Q.unrolledComponentHeightEquiv k u w).injective _).symm

end ASGinzburg.CutQuiver
