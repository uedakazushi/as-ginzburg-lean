import ASGinzburg.GinzburgPrefixLeftAction
import ASGinzburg.GinzburgGeneratorLayerHomology

/-! The actual append-generator comparison of prefix and associated
graded complexes commutes with genuine degree-zero left paths. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
open scoped Classical
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgAssociatedLeftTerm_mk {x y v : Q.LiftVertex} (r q : ℤ)
    (f : Q.ginzburgCutCohomologicalComponent k x.1 y.1 0 (y.2-x.2))
    (g : Q.ginzburgGeneratorFiltrationAtDegree k y.1 v.1 r q (v.2-y.2)) :
    Q.ginzburgAssociatedLeftTerm k (v:=v) r q f (Submodule.Quotient.mk g)=
      Submodule.Quotient.mk (Q.ginzburgFilteredLeftTerm k (v:=v) r q f g) := rfl

theorem ginzburgPrefixLeftTerm_piSingle {x y v : Q.LiftVertex} (r q : ℤ)
    (f : Q.ginzburgCutCohomologicalComponent k x.1 y.1 0 (y.2-x.2))
    (a : {a : Q.GinzburgArrow // a.target Q=v.1 ∧ a.cohomologicalDegree Q=r})
    (g : Q.ginzburgCutCohomologicalComponent k y.1 (a.val.source Q) (q-r)
      (v.2-y.2-a.val.cutDegree Q)) :
    Q.ginzburgPrefixLeftTerm k (v:=v) r q f (Pi.single a g)=
      Pi.single a ((Q.ginzburgPrefixLeftTerm k (v:=v) r q f (Pi.single a g)) a) := by
  funext b
  by_cases hb : a=b
  · subst b
    simp only [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne (Ne.symm hb)]
    apply Subtype.ext
    change Q.ginzburgPathComp k
      ((Pi.single a g : Q.GinzburgGeneratorPrefix k y.1 v.1 r q (v.2-y.2)) b).val f.val=0
    rw [Pi.single_eq_of_ne (Ne.symm hb)]
    simp

set_option maxHeartbeats 1000000 in
theorem ginzburgPrefixToGradedRow_left_naturality {x y v : Q.LiftVertex} (r q : ℤ)
    (f : Q.ginzburgCutCohomologicalComponent k x.1 y.1 0 (y.2-x.2)) :
    (Q.ginzburgAssociatedLeftTerm k (v:=v) r q f).comp
        (Q.ginzburgGeneratorPrefixToGradedRow k y.1 v.1 r q (v.2-y.2))=
      (Q.ginzburgGeneratorPrefixToGradedRow k x.1 v.1 r q (v.2-x.2)).comp
        (Q.ginzburgPrefixLeftTerm k (v:=v) r q f) := by
  rcases v with ⟨w,t⟩
  apply LinearMap.pi_ext
  intro a g
  change Q.ginzburgAssociatedLeftTerm k (v:=(w,t)) r q f
      (Q.ginzburgGeneratorPrefixToGradedRow k y.1 w r q (t-y.2) (Pi.single a g))=
    Q.ginzburgGeneratorPrefixToGradedRow k x.1 w r q (t-x.2)
      (Q.ginzburgPrefixLeftTerm k (v:=(w,t)) r q f (Pi.single a g))
  rw [Q.ginzburgGeneratorPrefixToGradedRow_piSingle,
    Q.ginzburgPrefixLeftTerm_piSingle,Q.ginzburgGeneratorPrefixToGradedRow_piSingle]
  obtain ⟨a,ht,hr⟩ := a
  change a.target Q=w at ht
  subst w
  subst r
  simp only [ginzburgGeneratorPrefixSingleClass,ginzburgGeneratorLayerClass,
    LinearMap.comp_apply,Submodule.mkQ_apply]
  rw [Q.ginzburgAssociatedLeftTerm_mk]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  let b := (Q.ginzburgPrefixLeftTerm k (v:=(a.target Q,t)) (a.cohomologicalDegree Q) q f
    (Pi.single ⟨a,rfl,rfl⟩ g)) ⟨a,rfl,rfl⟩
  have hb : b.val=Q.ginzburgPathComp k g.val f.val := by
    rw [Q.ginzburgPrefixLeftTerm_apply_coe,Pi.single_eq_same]
  change Q.ginzburgPathComp k
      (Q.ginzburgPathComp k (Finsupp.single (Q.ginzburgArrowPath a) 1) g.val) f.val=
    Q.ginzburgPathComp k (Finsupp.single (Q.ginzburgArrowPath a) 1) b.val
  rw [hb]
  exact (Q.ginzburgPathComp_assoc k _ _ _).symm

theorem ginzburgPrefixToAssociatedGraded_left_naturality (φ : Q.Potential k)
    {x y v : Q.LiftVertex} (r : ℤ)
    (f : Q.ginzburgCutCohomologicalComponent k x.1 y.1 0 (y.2-x.2)) :
    Q.ginzburgPrefixLeftCochainMap k φ r f ≫
        Q.ginzburgGeneratorPrefixToAssociatedGraded k φ x.1 v.1 r (v.2-x.2)=
      Q.ginzburgGeneratorPrefixToAssociatedGraded k φ y.1 v.1 r (v.2-y.2) ≫
        Q.ginzburgAssociatedLeftCochainMap k φ r f := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  exact (Q.ginzburgPrefixToGradedRow_left_naturality k (v:=v) r q f).symm

end ASGinzburg.CutQuiver
