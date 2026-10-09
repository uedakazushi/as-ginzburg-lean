import ASGinzburg.ASMinimalRelationSupport
import ASGinzburg.ASFirstKernelSupport

/-! The genuine minimal-relation/kernel-top comparison for all lifted
vertex pairs. Nonincreasing components are proved zero on both sides. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)
  (R : ∀ w : Q.LiftVertex, A.ASResolution Q w)

set_option synthInstance.maxHeartbeats 200000 in
noncomputable def presentationMinimalRelationFirstKernelTopEquiv_all
    (u w : Q.LiftVertex) :
    Q.MinimalRelationComponent (A.unrolledPathPresentation Q R).kernel
      (Q.height u) (Q.height w) ≃ₗ[k]
      ((A.rightModuleEvaluation (Q.height u)).obj (kernel (R w).d₁) ⧸
        A.positiveActionSpan (kernel (R w).d₁) (Q.height u)) := by
  classical
  by_cases huw : Q.height u < Q.height w
  · exact A.presentationMinimalRelationFirstKernelTopEquiv Q R u w huw
  · have hge := le_of_not_gt huw
    letI : Subsingleton (Q.MinimalRelationComponent (A.unrolledPathPresentation Q R).kernel
        (Q.height u) (Q.height w)) :=
      ⟨fun x y => by rw [A.minimalRelationComponent_eq_zero_of_ge Q R u w hge x,
        A.minimalRelationComponent_eq_zero_of_ge Q R u w hge y]⟩
    letI : Subsingleton ((A.rightModuleEvaluation (Q.height u)).obj (kernel (R w).d₁) ⧸
        A.positiveActionSpan (kernel (R w).d₁) (Q.height u)) :=
      ⟨fun x y => by
        have hz : ∀ z : (A.rightModuleEvaluation (Q.height u)).obj (kernel (R w).d₁) ⧸
            A.positiveActionSpan (kernel (R w).d₁) (Q.height u), z=0 := by
          intro z
          induction z using Submodule.Quotient.induction_on with
          | _ z =>
              rw [(R w).firstKernel_component_eq_zero_of_ge (Q.height u) hge z]
              simp
        rw [hz x,hz y]⟩
    exact LinearEquiv.ofSubsingleton (R := k) _ _

end ASGinzburg.ZAlgebra
