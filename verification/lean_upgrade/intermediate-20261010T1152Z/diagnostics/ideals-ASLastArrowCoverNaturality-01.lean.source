import ASGinzburg.ASLastArrowCoverMap
import ASGinzburg.UnrolledLastArrowProductCoordinates
import ASGinzburg.FiniteCoproductComponentNaturality

/-! Prefix multiplication corresponds to the existing right action
on the actual first AS term. This is needed for the JI/radical comparison. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)
  (R : ∀ w : Q.LiftVertex, A.ASResolution Q w)

theorem lastArrowToASFirstTerm_action {u v w : Q.LiftVertex}
    (huw : u≠w) (hvw : v≠w)
    (f : Q.UnrolledPathComponent k u v) (g : Q.UnrolledPathComponent k v w) :
    A.lastArrowToASFirstTerm Q R u w huw (Q.unrolledPathComp k g f)=
      (A.asResolutionTerm₁ Q w).obj.map
        (show (⟨Q.height u⟩ : A.Obj) ⟶ ⟨Q.height v⟩ from
          A.unrolledPathLinearEvaluation Q R u v f).op
        (A.lastArrowToASFirstTerm Q R v w hvw g) := by
  classical
  apply (A.rightFiniteCoproductPiEquiv
    (fun a : Q.incomingArrows w => A.representable (Q.height (Q.incomingSource w a)))
    (Q.height u)).injective
  funext a
  have ha := A.rightFiniteCoproductPiEquiv_action
    (fun a : Q.incomingArrows w => A.representable (Q.height (Q.incomingSource w a)))
    (Q.height u) (Q.height v) (A.unrolledPathLinearEvaluation Q R u v f)
    (A.lastArrowToASFirstTerm Q R v w hvw g) a
  refine Eq.trans ?_ ha.symm
  change (A.rightFiniteCoproductPiEquiv
    (fun a : Q.incomingArrows w => A.representable (Q.height (Q.incomingSource w a))) (Q.height u))
    ((A.rightFiniteCoproductPiEquiv
      (fun a : Q.incomingArrows w => A.representable (Q.height (Q.incomingSource w a))) (Q.height u)).symm
      (A.lastArrowPrefixEvaluation Q R u w
        (Q.unrolledLastArrowLinearEquiv k u w huw (Q.unrolledPathComp k g f)))) a=
    (A.representable (Q.height (Q.incomingSource w a))).obj.map
      (show (⟨Q.height u⟩ : A.Obj) ⟶ ⟨Q.height v⟩ from
        A.unrolledPathLinearEvaluation Q R u v f).op
      ((A.rightFiniteCoproductPiEquiv
        (fun a : Q.incomingArrows w => A.representable (Q.height (Q.incomingSource w a))) (Q.height v))
        ((A.rightFiniteCoproductPiEquiv
          (fun a : Q.incomingArrows w => A.representable (Q.height (Q.incomingSource w a))) (Q.height v)).symm
          (A.lastArrowPrefixEvaluation Q R v w (Q.unrolledLastArrowLinearEquiv k v w hvw g))) a)
  rw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
  change A.unrolledPathLinearEvaluation Q R u (Q.incomingSource w a)
    (Q.unrolledLastArrowLinearEquiv k u w huw (Q.unrolledPathComp k g f) a)=
      A.comp (A.unrolledPathLinearEvaluation Q R v (Q.incomingSource w a)
        (Q.unrolledLastArrowLinearEquiv k v w hvw g a))
        (A.unrolledPathLinearEvaluation Q R u v f)
  rw [Q.unrolledLastArrowLinearEquiv_comp,A.unrolledPathLinearEvaluation_comp]

end ASGinzburg.ZAlgebra
