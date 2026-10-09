import ASGinzburg.ZAlgebraFixedRepresentables
import ASGinzburg.ASResolution

/-! The genuine coproduct terms in the AS sequence are preserved by
explicit vertex-fixing transport, using preservation of actual coproducts. -/
namespace ASGinzburg.ZAlgebra.Isomorphism
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] {A B : ZAlgebra.{u,v} k}
variable (E : Isomorphism A B)

noncomputable def fixedRepresentableSumIso {ι : Type} (idx : ι→ℤ) :
    E.fixedRightModuleFunctor.obj (∐ fun a : ι => A.representable (idx a)) ≅
      ∐ fun a : ι => B.representable (idx a) :=
  PreservesCoproduct.iso E.fixedRightModuleFunctor _ ≪≫
    Sigma.mapIso (fun a => E.fixedRepresentableIso (idx a))

noncomputable def asResolutionTerm₁Iso (Q : CutQuiver) (v : Q.LiftVertex) :
    E.fixedRightModuleFunctor.obj (A.asResolutionTerm₁ Q v) ≅ B.asResolutionTerm₁ Q v :=
  E.fixedRepresentableSumIso (fun a : Q.incomingArrows v => Q.height (Q.incomingSource v a))

noncomputable def asResolutionTerm₂Iso (Q : CutQuiver) (v : Q.LiftVertex) :
    E.fixedRightModuleFunctor.obj (A.asResolutionTerm₂ Q v) ≅ B.asResolutionTerm₂ Q v :=
  E.fixedRepresentableSumIso (fun a : Q.outgoingArrows (Q.tau.symm v) =>
    Q.height (Q.outgoingTarget (Q.tau.symm v) a))

end ASGinzburg.ZAlgebra.Isomorphism
