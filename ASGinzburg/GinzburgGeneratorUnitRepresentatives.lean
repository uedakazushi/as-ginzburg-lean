import ASGinzburg.GinzburgGeneratorUnitHomologyClasses

/-! The genuine single-arrow filtered representatives are exactly
the unit basis cycles already identified in the existing projective terms. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgIncomingArrowPolynomial (v : Q.Vertex) (r : ℤ)
    (a : Q.GinzburgIncomingDegree v r) : Q.GinzburgPathComponent k (a.val.source Q) v :=
  Finsupp.single (GinzburgPath.transport Q rfl a.property.1 (Q.ginzburgArrowPath a.val)) 1

theorem ginzburgGeneratorPrefixSingleLayer_val (u v : Q.Vertex) (r q c : ℤ)
    (a : Q.GinzburgIncomingDegree v r)
    (f : Q.ginzburgCutCohomologicalComponent k u (a.val.source Q)
      (q-r) (c-a.val.cutDegree Q)) :
    (Q.ginzburgGeneratorPrefixSingleLayer k u v r q c a f).val=
      Q.ginzburgPathComp k (Q.ginzburgIncomingArrowPolynomial k v r a) f.val := by
  obtain ⟨a,ht,hr⟩ := a
  subst v
  subst r
  rfl

theorem ginzburgGeneratorUnitLayer_eq_singleClass (φ : Q.Potential k)
    (v : Q.LiftVertex) (r : ℤ) (a : Q.GinzburgIncomingDegree v.1 r) :
    Q.ginzburgGeneratorUnitLayer k φ v r a=
      Q.ginzburgGeneratorPrefixSingleClass k
        (Q.ginzburgPrefixGeneratorEndpoint v a.val).1 v.1 r r
        (v.2-(Q.ginzburgPrefixGeneratorEndpoint v a.val).2) a
        (Q.ginzburgGeneratorUnitPrefix k v r a) := by
  change Q.ginzburgGeneratorPrefixToGradedRow k
    (Q.ginzburgPrefixGeneratorEndpoint v a.val).1 v.1 r r
    (v.2-(Q.ginzburgPrefixGeneratorEndpoint v a.val).2)
      (Pi.single a (Q.ginzburgGeneratorUnitPrefix k v r a))=_
  exact Q.ginzburgGeneratorPrefixToGradedRow_piSingle k _ _ _ _ _ _ _

theorem ginzburgGeneratorPrefixSingleLayer_unit_val
    (v : Q.LiftVertex) (r : ℤ) (a : Q.GinzburgIncomingDegree v.1 r) :
    (Q.ginzburgGeneratorPrefixSingleLayer k
      (Q.ginzburgPrefixGeneratorEndpoint v a.val).1 v.1 r r
      (v.2-(Q.ginzburgPrefixGeneratorEndpoint v a.val).2) a
      (Q.ginzburgGeneratorUnitPrefix k v r a)).val=
      Q.ginzburgIncomingArrowPolynomial k v.1 r a := by
  rw [Q.ginzburgGeneratorPrefixSingleLayer_val,Q.ginzburgGeneratorUnitPrefix_val]
  change Q.ginzburgPathComp k (Q.ginzburgIncomingArrowPolynomial k v.1 r a)
    (Q.ginzburgPathId k (a.val.source Q))=_
  exact Q.id_ginzburgPathComp k _

theorem ginzburgGeneratorUnitLayer_eq_quotient_single (φ : Q.Potential k)
    (v : Q.LiftVertex) (r : ℤ) (a : Q.GinzburgIncomingDegree v.1 r)
    (f : Q.ginzburgGeneratorFiltrationAtDegree k
      (Q.ginzburgPrefixGeneratorEndpoint v a.val).1 v.1 r r
      (v.2-(Q.ginzburgPrefixGeneratorEndpoint v a.val).2))
    (hf : f.val=Q.ginzburgIncomingArrowPolynomial k v.1 r a) :
    Q.ginzburgGeneratorUnitLayer k φ v r a=Submodule.Quotient.mk f := by
  rw [Q.ginzburgGeneratorUnitLayer_eq_singleClass]
  change Submodule.Quotient.mk
    (Submodule.inclusion (Q.ginzburgGeneratorLayerAtDegree_le_filtration k _ _ _ _ _)
      (Q.ginzburgGeneratorPrefixSingleLayer k
        (Q.ginzburgPrefixGeneratorEndpoint v a.val).1 v.1 r r
        (v.2-(Q.ginzburgPrefixGeneratorEndpoint v a.val).2) a
        (Q.ginzburgGeneratorUnitPrefix k v r a)))=Submodule.Quotient.mk f
  congr 1
  apply Subtype.ext
  exact (Q.ginzburgGeneratorPrefixSingleLayer_unit_val k v r a).trans hf.symm

end ASGinzburg.CutQuiver
