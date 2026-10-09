import ASGinzburg.GinzburgSingleGeneratorRepresentatives
import ASGinzburg.GinzburgFilteredPrefixCoefficients

/-! The actual filtered-to-prefix map of every concrete unit generator
is its genuine single prefix unit family, at every degree and integer sheet. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgFilteredToPrefix_unitRepresentative (φ : Q.Potential k)
    (v : Q.LiftVertex) (r : ℤ) (a : Q.GinzburgIncomingDegree v.1 r) :
    (Q.ginzburgFilteredToPrefix k φ
      (Q.ginzburgPrefixGeneratorEndpoint v a.val).1 v.1 r
      (v.2-(Q.ginzburgPrefixGeneratorEndpoint v a.val).2)).f r
      (Q.ginzburgGeneratorUnitRepresentative k v r a)=
      Pi.single a (Q.ginzburgGeneratorUnitPrefix k v r a) := by
  let e := Q.ginzburgGeneratorPrefixGradedIso k φ
    (Q.ginzburgPrefixGeneratorEndpoint v a.val).1 v.1 r
    (v.2-(Q.ginzburgPrefixGeneratorEndpoint v a.val).2)
  change e.inv.f r (Submodule.Quotient.mk
    (Q.ginzburgGeneratorUnitRepresentative k v r a))=_
  have he := Q.ginzburgGeneratorUnitLayer_eq_quotient_single k φ v r a
    (Q.ginzburgGeneratorUnitRepresentative k v r a)
    (Q.ginzburgGeneratorUnitRepresentative_val k v r a)
  rw [←he]
  exact congrArg (fun f => f (Pi.single a (Q.ginzburgGeneratorUnitPrefix k v r a)))
    ((HomologicalComplex.eval (ModuleCat k) (ComplexShape.up ℤ) r).mapIso e).hom_inv_id

end ASGinzburg.CutQuiver
