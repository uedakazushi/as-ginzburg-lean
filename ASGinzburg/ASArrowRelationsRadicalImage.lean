import ASGinzburg.ASArrowRelationPreimageSpan
import ASGinzburg.ASPathRelationKernelNaturality
import ASGinzburg.ASFirstKernelSupport
import ASGinzburg.ASPathRelationSupport
import ASGinzburg.RightModuleRadical

/-! The actual image of JI under the relation-to-kernel map is exactly
the existing kernel's positive-action radical. Surjectivity and support
are derived from the original AS resolution, not added assumptions. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)
  (R : ∀ w : Q.LiftVertex, A.ASResolution Q w)

theorem pathArrowRelationProduct_map_eq_firstKernel_radical
    (u w : Q.LiftVertex) (huw : Q.height u < Q.height w) :
    Submodule.map (A.pathRelationsToCategoricalASFirstKernel Q R u w
      (by intro h; subst w; exact lt_irrefl _ huw))
      (Submodule.comap (LinearMap.ker (A.unrolledPathLinearEvaluation Q R u w)).subtype
        (A.pathArrowRelationProduct Q R u w))=
          A.positiveActionSpan (kernel (R w).d₁) (Q.height u) := by
  classical
  have hne : u≠w := by intro h; subst w; exact lt_irrefl _ huw
  apply le_antisymm
  · rw [A.pathArrowRelationProduct_subtype_preimage_span,Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro y ⟨r,⟨v,f,hf,g,hg,hcomp⟩,rfl⟩
    by_cases huv : Q.height u < Q.height v
    · by_cases hvw : v≠w
      · let g' : LinearMap.ker (A.unrolledPathLinearEvaluation Q R v w) := ⟨g,hg⟩
        have hr : r=A.prependPathRelation Q R f g' := Subtype.ext hcomp.symm
        rw [hr,A.pathRelationsToCategoricalASFirstKernel_action Q R hne hvw f g']
        apply Submodule.subset_span
        exact ⟨Q.height v,huv,A.pathRelationsToCategoricalASFirstKernel Q R v w hvw g',
          A.unrolledPathLinearEvaluation Q R u v f,rfl⟩
      · have hv : v=w := Classical.not_not.mp hvw
        subst v
        have hg0 : g=0 := A.unrolledPathLinearEvaluation_ker_eq_zero_of_ge Q R w w le_rfl ⟨g,hg⟩
        have hr : r=0 := Subtype.ext (by rw [←hcomp,hg0]; simp)
        rw [hr,map_zero]
        exact (A.positiveActionSpan (kernel (R w).d₁) (Q.height u)).zero_mem
    · have hf0 := Q.unrolledPositivePath_eq_zero_of_ge k (le_of_not_gt huv) f hf
      have hr : r=0 := Subtype.ext (by rw [←hcomp,hf0]; simp)
      rw [hr,map_zero]
      exact (A.positiveActionSpan (kernel (R w).d₁) (Q.height u)).zero_mem
  · apply Submodule.span_le.mpr
    rintro y ⟨l,hl,x,a,rfl⟩
    obtain ⟨v,rfl⟩ := Q.height_bijective.surjective l
    by_cases hv : Q.height w ≤ Q.height v
    · rw [(R w).firstKernel_component_eq_zero_of_ge (Q.height v) hv x,map_zero]
      exact (Submodule.map _ _).zero_mem
    · have hvw : v≠w := by intro h; subst v; exact hv le_rfl
      obtain ⟨g,hg⟩ := A.pathRelationsToCategoricalASFirstKernel_surjective Q R v w hvw x
      obtain ⟨f,hf⟩ := A.unrolledPathLinearEvaluation_surjective Q R u v a
      apply Submodule.mem_map.mpr
      refine ⟨A.prependPathRelation Q R f g,?_,?_⟩
      · apply Submodule.subset_span
        exact ⟨v,f,Q.unrolledPositivePath_mem_of_height_lt k hl f,g.val,g.property,rfl⟩
      · rw [A.pathRelationsToCategoricalASFirstKernel_action Q R hne hvw f g,hf,hg]

end ASGinzburg.ZAlgebra
