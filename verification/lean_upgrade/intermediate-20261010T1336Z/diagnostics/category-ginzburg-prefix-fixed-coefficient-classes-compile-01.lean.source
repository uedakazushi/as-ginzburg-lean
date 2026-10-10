import ASGinzburg.GinzburgPrefixFixedCoefficients

/-! Arithmetic endpoint transport preserves actual coefficient classes
and the actual degree-zero path products in the prefix family. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgPrefixCoefficientZeroCutEquiv (x v : Q.LiftVertex)
    (a : Q.GinzburgArrow) :
    Q.ginzburgCutCohomologicalComponent k x.1 (a.source Q) 0 (v.2-x.2-a.cutDegree Q) ≃ₗ[k]
      Q.ginzburgCutCohomologicalComponent k x.1 (a.source Q) 0
        ((v.2-a.cutDegree Q)-x.2) :=
  Q.ginzburgCutZeroEquivOfCutEq k x.1 (a.source Q)
    (v.2-x.2-a.cutDegree Q) ((v.2-a.cutDegree Q)-x.2) (by omega)

theorem ginzburgPrefixCoefficientZeroCutEquiv_coe (x v : Q.LiftVertex)
    (a : Q.GinzburgArrow)
    (g : Q.ginzburgCutCohomologicalComponent k x.1 (a.source Q) 0 (v.2-x.2-a.cutDegree Q)) :
    (Q.ginzburgPrefixCoefficientZeroCutEquiv k x v a g).val=g.val :=
  Q.ginzburgCutZeroEquivOfCutEq_apply_coe k x.1 (a.source Q) _ _ _ g

theorem ginzburgPrefixCoefficientFixedUnrolledEquiv_mk (φ : Q.Potential k)
    (x v : Q.LiftVertex) (a : Q.GinzburgArrow)
    (g : Q.ginzburgCutCohomologicalComponent k x.1 (a.source Q) 0 (v.2-x.2-a.cutDegree Q)) :
    Q.ginzburgPrefixCoefficientFixedUnrolledEquiv k φ x v a (Submodule.Quotient.mk g)=
      Q.ginzburgCutZeroQuotientUnrolledEquiv k φ x (Q.ginzburgPrefixGeneratorEndpoint v a)
        (Submodule.Quotient.mk (Q.ginzburgPrefixCoefficientZeroCutEquiv k x v a g)) := by
  simp only [ginzburgPrefixCoefficientFixedUnrolledEquiv,LinearEquiv.trans_apply,
    ginzburgPrefixCoefficientCutEquiv]
  apply congrArg (Q.ginzburgCutZeroQuotientUnrolledEquiv k φ x
    (Q.ginzburgPrefixGeneratorEndpoint v a))
  exact Q.ginzburgCutZeroQuotientEquivOfCutEq_mk k φ x.1 (a.source Q)
    (v.2-x.2-a.cutDegree Q) ((v.2-a.cutDegree Q)-x.2) (by omega) g

theorem ginzburgPrefixCoefficientZeroCutEquiv_leftTerm {x y v : Q.LiftVertex} (r : ℤ)
    (f : Q.ginzburgCutCohomologicalComponent k x.1 y.1 0 (y.2-x.2))
    (g : Q.GinzburgGeneratorPrefix k y.1 v.1 r r (v.2-y.2))
    (a : {a : Q.GinzburgArrow // a.target Q=v.1 ∧ a.cohomologicalDegree Q=r}) :
    Q.ginzburgPrefixCoefficientZeroCutEquiv k x v a.val
        (Q.ginzburgGeneratorPrefixTopEquiv k x.1 v.1 r (v.2-x.2)
          (Q.ginzburgPrefixLeftTerm k r r f g) a)=
      Q.ginzburgCutZeroComp k (u:=x) (v:=y) (w:=Q.ginzburgPrefixGeneratorEndpoint v a.val)
        (Q.ginzburgPrefixCoefficientZeroCutEquiv k y v a.val
          (Q.ginzburgGeneratorPrefixTopEquiv k y.1 v.1 r (v.2-y.2) g a)) f := by
  apply Subtype.ext
  change _=Q.ginzburgPathComp k
    (Q.ginzburgPrefixCoefficientZeroCutEquiv k y v a.val
      (Q.ginzburgGeneratorPrefixTopEquiv k y.1 v.1 r (v.2-y.2) g a)).val f.val
  rw [Q.ginzburgPrefixCoefficientZeroCutEquiv_coe,
    Q.ginzburgPrefixCoefficientZeroCutEquiv_coe]
  exact Q.ginzburgPrefixTopEquiv_leftTerm_coe k r f g a

end ASGinzburg.CutQuiver
