import ASGinzburg.GinzburgGeneratorAppendCoefficients

/-! The genuine generator/prefix linear equivalence inverts the
actual maps that adjoin a last generator. -/
namespace ASGinzburg.CutQuiver
open scoped Classical
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgGeneratorLayerFreeEquiv_prefixSingleLayer (u v : Q.Vertex) (r q c : ℤ)
    (a : {a : Q.GinzburgArrow // a.target Q=v ∧ a.cohomologicalDegree Q=r})
    (f : Q.ginzburgCutCohomologicalComponent k u (a.val.source Q) (q-r) (c-a.val.cutDegree Q)) :
    Q.ginzburgGeneratorLayerFreeEquiv k u v r q c
      (Q.ginzburgGeneratorPrefixSingleLayer k u v r q c a f)=Pi.single a f := by
  obtain ⟨a,ht,hr⟩ := a
  subst v
  subst r
  funext b
  apply (Q.ginzburgCutComponentBasisEquiv k u (b.val.source Q)
    (q-a.cohomologicalDegree Q) (c-b.val.cutDegree Q)).injective
  apply Finsupp.ext
  intro p
  simp only [Q.ginzburgCutComponentBasisEquiv_apply]
  rw [Q.ginzburgGeneratorLayerFreeEquiv_apply]
  by_cases hb : b=⟨a,rfl,rfl⟩
  · subst b
    simp only [Pi.single_eq_same]
    change Q.ginzburgPathComp k (Finsupp.single (Q.ginzburgArrowPath a) 1) f.val
      (GinzburgPath.snoc p.val a rfl)=f.val p.val
    exact Q.ginzburgAppendGenerator_coefficient k a u f.val p.val
  · rw [Pi.single_eq_of_ne hb]
    change Q.ginzburgPathComp k (Finsupp.single (Q.ginzburgArrowPath a) 1) f.val
      ((GinzburgLastGeneratorData.path Q) ⟨⟨b.val,b.property.1⟩,p.val⟩)=0
    apply Q.ginzburgAppendGenerator_coefficient_other k a u f.val
    intro he
    exact hb (Subtype.ext he)

theorem ginzburgGeneratorLayerFreeEquiv_symm_piSingle (u v : Q.Vertex) (r q c : ℤ)
    (a : {a : Q.GinzburgArrow // a.target Q=v ∧ a.cohomologicalDegree Q=r})
    (f : Q.ginzburgCutCohomologicalComponent k u (a.val.source Q) (q-r) (c-a.val.cutDegree Q)) :
    (Q.ginzburgGeneratorLayerFreeEquiv k u v r q c).symm (Pi.single a f)=
      Q.ginzburgGeneratorPrefixSingleLayer k u v r q c a f := by
  apply (Q.ginzburgGeneratorLayerFreeEquiv k u v r q c).injective
  rw [LinearEquiv.apply_symm_apply,Q.ginzburgGeneratorLayerFreeEquiv_prefixSingleLayer]

theorem ginzburgGeneratorPrefixToGradedRow_eq_equiv (u v : Q.Vertex) (r q c : ℤ) :
    Q.ginzburgGeneratorPrefixToGradedRow k u v r q c=
      ((Q.ginzburgGeneratorLayerFreeEquiv k u v r q c).symm.trans
        (Q.ginzburgGeneratorLayerQuotientEquiv k u v r q c).symm).toLinearMap := by
  apply LinearMap.pi_ext
  intro a f
  rw [Q.ginzburgGeneratorPrefixToGradedRow_piSingle]
  change Q.ginzburgGeneratorPrefixSingleClass k u v r q c a f=
    (Q.ginzburgGeneratorLayerQuotientEquiv k u v r q c).symm
      ((Q.ginzburgGeneratorLayerFreeEquiv k u v r q c).symm (Pi.single a f))
  rw [Q.ginzburgGeneratorLayerFreeEquiv_symm_piSingle,
    Q.ginzburgGeneratorLayerQuotientEquiv_symm]
  rfl

theorem ginzburgGeneratorPrefixToGradedRow_bijective (u v : Q.Vertex) (r q c : ℤ) :
    Function.Bijective (Q.ginzburgGeneratorPrefixToGradedRow k u v r q c) := by
  rw [Q.ginzburgGeneratorPrefixToGradedRow_eq_equiv]
  exact ((Q.ginzburgGeneratorLayerFreeEquiv k u v r q c).symm.trans
    (Q.ginzburgGeneratorLayerQuotientEquiv k u v r q c).symm).bijective

end ASGinzburg.CutQuiver
