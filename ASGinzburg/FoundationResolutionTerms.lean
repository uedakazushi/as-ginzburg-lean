import ASGinzburg.FoundationRestrictedResolution
import ASGinzburg.FoundationSurvivingArrows
import ASGinzburg.CoproductDropZero

/-! The first two actual restricted AS terms are precisely the non-cut
incoming and cut outgoing finite sums occurring in the paper's (3.5). -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

def foundationRepresentable (j : Q.Vertex) : A.FoundationRightModule Q :=
  (A.foundationRestriction Q).obj (A.representable (j.val : ℤ))

noncomputable def foundationFirstTerm (j : Q.Vertex) : A.FoundationRightModule Q :=
  ∐ fun a : {a : Q.incomingArrows (j,0) // Q.cut a.val=false} =>
    A.foundationRepresentable Q (Q.source a.val.val)

noncomputable def foundationSecondTerm (j : Q.Vertex) : A.FoundationRightModule Q :=
  ∐ fun a : {a : Q.outgoingArrows (Q.tau.symm (j,0)) // Q.cut a.val=true} =>
    A.foundationRepresentable Q (Q.target a.val.val)

noncomputable def foundationASFirstTermIso (j : Q.Vertex) :
    (A.foundationRestriction Q).obj (A.asResolutionTerm₁ Q (j,0)) ≅
      A.foundationFirstTerm Q j := by
  classical
  let g := fun a : Q.incomingArrows (j,0) =>
    (A.foundationRestriction Q).obj
      (A.representable (Q.height (Q.incomingSource (j,0) a)))
  have hz : ∀ a, ¬Q.cut a.val=false → IsZero (g a) := by
    intro a ha
    apply A.foundation_representable_isZero_of_neg Q
    exact lt_of_not_ge (fun h => ha ((Q.foundation_incoming_nonnegative_iff j a).mp h))
  refine PreservesCoproduct.iso (A.foundationRestriction Q)
    (fun a : Q.incomingArrows (j,0) =>
      A.representable (Q.height (Q.incomingSource (j,0) a))) ≪≫
    coproductDropZeroIso g (fun a => Q.cut a.val=false) hz ≪≫ ?_
  apply eqToIso
  congr 1
  funext a
  simp [g,foundationRepresentable,CutQuiver.incomingSource,CutQuiver.liftedSource,
    CutQuiver.height,CutQuiver.cutDegree,a.property]

noncomputable def foundationASSecondTermIso (j : Q.Vertex) :
    (A.foundationRestriction Q).obj (A.asResolutionTerm₂ Q (j,0)) ≅
      A.foundationSecondTerm Q j := by
  classical
  let g := fun a : Q.outgoingArrows (Q.tau.symm (j,0)) =>
    (A.foundationRestriction Q).obj
      (A.representable (Q.height (Q.outgoingTarget (Q.tau.symm (j,0)) a)))
  have hz : ∀ a, ¬Q.cut a.val=true → IsZero (g a) := by
    intro a ha
    apply A.foundation_representable_isZero_of_neg Q
    exact lt_of_not_ge (fun h => ha ((Q.foundation_outgoing_nonnegative_iff j a).mp h))
  refine PreservesCoproduct.iso (A.foundationRestriction Q)
    (fun a : Q.outgoingArrows (Q.tau.symm (j,0)) =>
      A.representable (Q.height (Q.outgoingTarget (Q.tau.symm (j,0)) a))) ≪≫
    coproductDropZeroIso g (fun a => Q.cut a.val=true) hz ≪≫ ?_
  apply eqToIso
  congr 1
  funext a
  simp [g,foundationRepresentable,CutQuiver.outgoingTarget,CutQuiver.liftedTarget,
    CutQuiver.tau,CutQuiver.shift,CutQuiver.height,CutQuiver.cutDegree,a.property]

end ASGinzburg.ZAlgebra
