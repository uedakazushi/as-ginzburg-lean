import ASGinzburg.ASLastArrowCoverMap

/-! Actual free-path relations surject onto the genuine componentwise
kernel of the first AS differential. No relation-top comparison is
assumed; the remaining denominator identification is a further proof. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)
  (R : ∀ w : Q.LiftVertex, A.ASResolution Q w)

noncomputable def pathRelationsToASFirstKernel (u w : Q.LiftVertex) (huw : u≠w) :
    LinearMap.ker (A.unrolledPathLinearEvaluation Q R u w) →ₗ[k]
      LinearMap.ker ((A.rightModuleEvaluation (Q.height u)).map (R w).d₁).hom :=
  ((A.lastArrowToASFirstTerm Q R u w huw).comp
    (LinearMap.ker (A.unrolledPathLinearEvaluation Q R u w)).subtype).codRestrict _ (by
      intro f
      change ((A.rightModuleEvaluation (Q.height u)).map (R w).d₁).hom
        (A.lastArrowToASFirstTerm Q R u w huw f.val)=0
      rw [A.lastArrowToASFirstTerm_d₁]
      exact f.property)

theorem pathRelationsToASFirstKernel_surjective (u w : Q.LiftVertex) (huw : u≠w) :
    Function.Surjective (A.pathRelationsToASFirstKernel Q R u w huw) := by
  intro x
  obtain ⟨f,hf⟩ := A.lastArrowToASFirstTerm_surjective Q R u w huw x.val
  have he : A.unrolledPathLinearEvaluation Q R u w f=0 := by
    rw [←A.lastArrowToASFirstTerm_d₁ Q R u w huw f,hf]
    exact x.property
  exact ⟨⟨f,he⟩,Subtype.ext hf⟩

theorem pathRelationsToASFirstKernel_ker (u w : Q.LiftVertex) (huw : u≠w) :
    LinearMap.ker (A.pathRelationsToASFirstKernel Q R u w huw)=
      Submodule.comap (LinearMap.ker (A.unrolledPathLinearEvaluation Q R u w)).subtype
        (LinearMap.ker (A.lastArrowToASFirstTerm Q R u w huw)) := by
  ext f
  change (⟨A.lastArrowToASFirstTerm Q R u w huw f.val,_⟩ :
    LinearMap.ker ((A.rightModuleEvaluation (Q.height u)).map (R w).d₁).hom)=0 ↔
      A.lastArrowToASFirstTerm Q R u w huw f.val=0
  exact Subtype.ext_iff

noncomputable def pathRelationsFirstKernelEquiv (u w : Q.LiftVertex) (huw : u≠w) :
    (LinearMap.ker (A.unrolledPathLinearEvaluation Q R u w) ⧸
      LinearMap.ker (A.pathRelationsToASFirstKernel Q R u w huw)) ≃ₗ[k]
        LinearMap.ker ((A.rightModuleEvaluation (Q.height u)).map (R w).d₁).hom :=
  (A.pathRelationsToASFirstKernel Q R u w huw).quotKerEquivOfSurjective
    (A.pathRelationsToASFirstKernel_surjective Q R u w huw)

end ASGinzburg.ZAlgebra
