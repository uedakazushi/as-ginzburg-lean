import ASGinzburg.ASFirstDifferentialCoordinates

/-! A genuine surjection from free paths onto the first AS projective
term, whose composition with d₁ is the original path evaluation. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)
  (R : ∀ w : Q.LiftVertex, A.ASResolution Q w)

noncomputable def lastArrowPrefixEvaluation (u w : Q.LiftVertex) :
    (∀ a : Q.incomingArrows w, Q.UnrolledPathComponent k u (Q.incomingSource w a)) →ₗ[k]
      (∀ a : Q.incomingArrows w, A.Hom (Q.height u) (Q.height (Q.incomingSource w a))) :=
  LinearMap.pi (fun a => (A.unrolledPathLinearEvaluation Q R u (Q.incomingSource w a)).comp
    (LinearMap.proj a))

noncomputable def lastArrowToASFirstTerm (u w : Q.LiftVertex) (huw : u≠w) :
    Q.UnrolledPathComponent k u w →ₗ[k]
      (A.rightModuleEvaluation (Q.height u)).obj (A.asResolutionTerm₁ Q w) :=
  (A.rightFiniteCoproductPiEquiv
    (fun a : Q.incomingArrows w => A.representable (Q.height (Q.incomingSource w a)))
    (Q.height u)).symm.toLinearMap.comp
      ((A.lastArrowPrefixEvaluation Q R u w).comp
        (Q.unrolledLastArrowLinearEquiv k u w huw).toLinearMap)

theorem lastArrowToASFirstTerm_surjective (u w : Q.LiftVertex) (huw : u≠w) :
    Function.Surjective (A.lastArrowToASFirstTerm Q R u w huw) := by
  classical
  intro x
  let y := A.rightFiniteCoproductPiEquiv
    (fun a : Q.incomingArrows w => A.representable (Q.height (Q.incomingSource w a)))
    (Q.height u) x
  let p : ∀ a : Q.incomingArrows w, Q.UnrolledPathComponent k u (Q.incomingSource w a) :=
    fun a => Classical.choose (A.unrolledPathLinearEvaluation_surjective Q R u
      (Q.incomingSource w a) (y a))
  refine ⟨(Q.unrolledLastArrowLinearEquiv k u w huw).symm p,?_⟩
  have hp : A.lastArrowPrefixEvaluation Q R u w p=y := by
    funext a
    exact Classical.choose_spec (A.unrolledPathLinearEvaluation_surjective Q R u
      (Q.incomingSource w a) (y a))
  change (A.rightFiniteCoproductPiEquiv
    (fun a : Q.incomingArrows w => A.representable (Q.height (Q.incomingSource w a)))
    (Q.height u)).symm (A.lastArrowPrefixEvaluation Q R u w
      ((Q.unrolledLastArrowLinearEquiv k u w huw)
        ((Q.unrolledLastArrowLinearEquiv k u w huw).symm p)))=x
  rw [LinearEquiv.apply_symm_apply,hp,LinearEquiv.symm_apply_apply]

theorem lastArrowToASFirstTerm_d₁ (u w : Q.LiftVertex) (huw : u≠w)
    (f : Q.UnrolledPathComponent k u w) :
    ((A.rightModuleEvaluation (Q.height u)).map (R w).d₁).hom
      (A.lastArrowToASFirstTerm Q R u w huw f)=A.unrolledPathLinearEvaluation Q R u w f := by
  change ((A.rightModuleEvaluation (Q.height u)).map (R w).d₁).hom
    ((A.rightFiniteCoproductPiEquiv _ _).symm
      (A.lastArrowPrefixEvaluation Q R u w (Q.unrolledLastArrowLinearEquiv k u w huw f)))=_
  rw [(R w).d₁_component_pi_symm,A.unrolledPathLinearEvaluation_lastArrow Q R u w huw]
  rfl

end ASGinzburg.ZAlgebra
