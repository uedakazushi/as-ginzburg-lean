import ASGinzburg.GinzburgGeneratorProjectiveModules

/-! The genuine generator projective modules at degrees zero and
negative one are isomorphic to the existing AS terms in the right-module
category itself. Only actual index equivalences and endpoint equalities
are used. -/
namespace ASGinzburg.CutQuiver
variable (Q : CutQuiver)

theorem ginzburgOriginalGeneratorEndpoint (v : Q.LiftVertex) (a : Q.incomingArrows v) :
    Q.ginzburgPrefixGeneratorEndpoint v (Q.ginzburgOriginalGeneratorEquiv v a).val=
      Q.incomingSource v a := rfl

theorem ginzburgDualGeneratorEndpoint (v : Q.LiftVertex)
    (a : Q.outgoingArrows (Q.tau.symm v)) :
    Q.ginzburgPrefixGeneratorEndpoint v (Q.ginzburgDualGeneratorEquiv v a).val=
      Q.outgoingTarget (Q.tau.symm v) a := by
  apply Prod.ext
  · rfl
  · change v.2-(1-Q.cutDegree a.val)=(v.2-1)+Q.cutDegree a.val
    omega

theorem ginzburgLoopGeneratorEndpoint (v : Q.LiftVertex) (a : PUnit.{1}) :
    Q.ginzburgPrefixGeneratorEndpoint v (Q.ginzburgLoopGeneratorEquiv v a).val=
      Q.tau.symm v := rfl

end ASGinzburg.CutQuiver

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def ginzburgGeneratorOriginalTermIso (w : Q.LiftVertex) :
    A.ginzburgGeneratorCoefficientModule Q w 0 ≅ A.asResolutionTerm₁ Q w :=
  (Sigma.whiskerEquiv (Q.ginzburgOriginalGeneratorEquiv w)
    (f:=fun a : Q.incomingArrows w => A.representable (Q.height (Q.incomingSource w a)))
    (g:=fun a : Q.GinzburgIncomingDegree w.1 0 =>
      A.representable (Q.height (Q.ginzburgPrefixGeneratorEndpoint w a.val)))
    (fun a => eqToIso (congrArg (fun z => A.representable (Q.height z))
      (Q.ginzburgOriginalGeneratorEndpoint w a)))).symm

noncomputable def ginzburgGeneratorDualTermIso (w : Q.LiftVertex) :
    A.ginzburgGeneratorCoefficientModule Q w (-1) ≅ A.asResolutionTerm₂ Q w :=
  (Sigma.whiskerEquiv (Q.ginzburgDualGeneratorEquiv w)
    (f:=fun a : Q.outgoingArrows (Q.tau.symm w) =>
      A.representable (Q.height (Q.outgoingTarget (Q.tau.symm w) a)))
    (g:=fun a : Q.GinzburgIncomingDegree w.1 (-1) =>
      A.representable (Q.height (Q.ginzburgPrefixGeneratorEndpoint w a.val)))
    (fun a => eqToIso (congrArg (fun z => A.representable (Q.height z))
      (Q.ginzburgDualGeneratorEndpoint w a)))).symm

end ASGinzburg.ZAlgebra
