import ASGinzburg.GinzburgPrefixTopNaturality

/-! Explicit coefficient classes in the actual finite quotient-family
presentation of top prefix homology. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
open scoped Classical
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgPrefixTopQuotientFamilyEquiv_mk (φ : Q.Potential k)
    (u v : Q.Vertex) (r c : ℤ) (g : Q.GinzburgGeneratorPrefix k u v r r c) :
    Q.ginzburgGeneratorPrefixTopQuotientFamilyEquiv k φ u v r c (Submodule.Quotient.mk g)=
      fun a => Submodule.Quotient.mk (Q.ginzburgGeneratorPrefixTopEquiv k u v r c g a) := rfl

theorem ginzburgPrefixTopQuotientFamilyEquiv_quotientMap_mk (φ : Q.Potential k)
    {x y v : Q.LiftVertex} (r : ℤ)
    (f : Q.ginzburgCutCohomologicalComponent k x.1 y.1 0 (y.2-x.2))
    (g : Q.GinzburgGeneratorPrefix k y.1 v.1 r r (v.2-y.2)) :
    Q.ginzburgGeneratorPrefixTopQuotientFamilyEquiv k φ x.1 v.1 r (v.2-x.2)
        (moduleCatShortComplexQuotientMap
          (Q.ginzburgPrefixTopShortComplexLeftMap k φ (v:=v) r f) (Submodule.Quotient.mk g))=
      fun a => Submodule.Quotient.mk
        (Q.ginzburgGeneratorPrefixTopEquiv k x.1 v.1 r (v.2-x.2)
          (Q.ginzburgPrefixLeftTerm k r r f g) a) := rfl

theorem ginzburgPrefixTopEquiv_leftTerm_coe {x y v : Q.LiftVertex} (r : ℤ)
    (f : Q.ginzburgCutCohomologicalComponent k x.1 y.1 0 (y.2-x.2))
    (g : Q.GinzburgGeneratorPrefix k y.1 v.1 r r (v.2-y.2))
    (a : {a : Q.GinzburgArrow // a.target Q=v.1 ∧ a.cohomologicalDegree Q=r}) :
    (Q.ginzburgGeneratorPrefixTopEquiv k x.1 v.1 r (v.2-x.2)
        (Q.ginzburgPrefixLeftTerm k r r f g) a).val=
      Q.ginzburgPathComp k
        (Q.ginzburgGeneratorPrefixTopEquiv k y.1 v.1 r (v.2-y.2) g a).val f.val := by
  rw [Q.ginzburgGeneratorPrefixTopEquiv_apply_coe,
    Q.ginzburgPrefixLeftTerm_apply_coe,Q.ginzburgGeneratorPrefixTopEquiv_apply_coe]

end ASGinzburg.CutQuiver
