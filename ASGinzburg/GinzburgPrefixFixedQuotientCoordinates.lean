import ASGinzburg.GinzburgPrefixFixedFamilyAction
import ASGinzburg.GinzburgGeneratorIndices

/-! Each genuine finite prefix quotient has the expected coordinate
in the actual fixed-endpoint Jacobian component comparison. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgPrefixTopFixedUnrolledEquiv_mk_apply (φ : Q.Potential k)
    (x v : Q.LiftVertex) (r : ℤ)
    (g : Q.GinzburgGeneratorPrefix k x.1 v.1 r r (v.2-x.2))
    (a : Q.GinzburgIncomingDegree v.1 r) :
    Q.ginzburgPrefixTopFixedUnrolledEquiv k φ x v r (Submodule.Quotient.mk g) a=
      Q.ginzburgPrefixCoefficientFixedUnrolledEquiv k φ x v a.val
        (Submodule.Quotient.mk
          (Q.ginzburgGeneratorPrefixTopEquiv k x.1 v.1 r (v.2-x.2) g a)) := by
  change Q.ginzburgPrefixCoefficientFixedUnrolledEquiv k φ x v a.val
    (Q.ginzburgGeneratorPrefixTopQuotientFamilyEquiv k φ x.1 v.1 r (v.2-x.2)
      (Submodule.Quotient.mk g) a)=_
  rw [Q.ginzburgPrefixTopQuotientFamilyEquiv_mk]

end ASGinzburg.CutQuiver
