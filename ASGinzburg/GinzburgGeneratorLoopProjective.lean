import ASGinzburg.GinzburgGeneratorProjectiveTerms

/-! The actual loop generator projective module is the existing
representable at the previous sheet, in the actual right-module category. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def ginzburgGeneratorLoopTermIso (w : Q.LiftVertex) :
    A.ginzburgGeneratorCoefficientModule Q w (-2) ≅
      A.representable (Q.height (Q.tau.symm w)) :=
  (Sigma.whiskerEquiv (Q.ginzburgLoopGeneratorEquiv w)
    (f:=fun _a : PUnit.{1} => A.representable (Q.height (Q.tau.symm w)))
    (g:=fun a : Q.GinzburgIncomingDegree w.1 (-2) =>
      A.representable (Q.height (Q.ginzburgPrefixGeneratorEndpoint w a.val)))
    (fun a => eqToIso (congrArg (fun z => A.representable (Q.height z))
      (Q.ginzburgLoopGeneratorEndpoint w a)))).symm ≪≫
    coproductUniqueIso (fun _a : PUnit.{1} => A.representable (Q.height (Q.tau.symm w)))

end ASGinzburg.ZAlgebra
