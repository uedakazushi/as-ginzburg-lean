import ASGinzburg.ASArrowRelationsRadicalImage
import ASGinzburg.ASRelationKernelHeightEquiv

/-! The radical preimage is the sum of genuine JI relations and the
IJ cover kernel. Height transport preserves the JI denominator too. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)
  (R : ∀ w : Q.LiftVertex, A.ASResolution Q w)

theorem pathRelationsToCategoricalASFirstKernel_ker (u w : Q.LiftVertex) (huw : u≠w) :
    LinearMap.ker (A.pathRelationsToCategoricalASFirstKernel Q R u w huw)=
      LinearMap.ker (A.pathRelationsToASFirstKernel Q R u w huw) := by
  ext x
  change (A.asFirstKernelComponentEquiv Q R u w).symm
    (A.pathRelationsToASFirstKernel Q R u w huw x)=0 ↔
      A.pathRelationsToASFirstKernel Q R u w huw x=0
  exact (A.asFirstKernelComponentEquiv Q R u w).symm.map_eq_zero_iff

theorem pathRelationHeightEquiv_map_arrowRelation_denominator (u w : Q.LiftVertex) :
    Submodule.map (A.pathRelationHeightEquiv Q R u w).toLinearMap
      (Submodule.comap (LinearMap.ker (A.unrolledPathLinearEvaluation Q R u w)).subtype
        (A.pathArrowRelationProduct Q R u w))=
      Submodule.comap ((A.unrolledPathPresentation Q R).kernel.hom
        (Q.height u) (Q.height w)).subtype
        (((Q.unrolledArrowIdeal k).mul (A.unrolledPathPresentation Q R).kernel).hom
          (Q.height u) (Q.height w)) := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    rw [A.pathArrowRelationProduct_eq_comap] at hx
    exact hx
  · intro hy
    obtain ⟨x,rfl⟩ := (A.pathRelationHeightEquiv Q R u w).surjective y
    apply Submodule.mem_map.mpr
    refine ⟨x,?_,rfl⟩
    rw [A.pathArrowRelationProduct_eq_comap]
    exact hy

theorem firstKernel_radical_preimage (u w : Q.LiftVertex)
    (huw : Q.height u < Q.height w) :
    Submodule.comap (A.pathRelationsToCategoricalASFirstKernel Q R u w
      (by intro h; subst w; exact lt_irrefl _ huw))
      (A.positiveActionSpan (kernel (R w).d₁) (Q.height u))=
      Submodule.comap (LinearMap.ker (A.unrolledPathLinearEvaluation Q R u w)).subtype
        (A.pathArrowRelationProduct Q R u w) ⊔
      LinearMap.ker (A.pathRelationsToASFirstKernel Q R u w
        (by intro h; subst w; exact lt_irrefl _ huw)) := by
  rw [←A.pathArrowRelationProduct_map_eq_firstKernel_radical Q R u w huw,
    Submodule.comap_map_eq,A.pathRelationsToCategoricalASFirstKernel_ker]

end ASGinzburg.ZAlgebra
