import ASGinzburg.GinzburgUnitHessianPrefixes
import ASGinzburg.GinzburgPrefixFixedQuotientCoordinates

/-! The actual native second projective differential has the actual
path-valued cyclic Hessian as its Jacobian quotient matrix entries. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgDualOriginalProjectiveMap_hessian_entry (φ : Q.Potential k)
    (a b : Q.Arrow) (s : ℤ) (hb : Q.target b=Q.source a) :
    ((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientComponentEquiv Q (Q.source a,s) 0
      (Q.height (Q.ginzburgPrefixGeneratorEndpoint (Q.source a,s) (.dual a)))
      (((Q.unrolledJacobianZAlgebra k φ).rightModuleEvaluation
        (Q.height (Q.ginzburgPrefixGeneratorEndpoint (Q.source a,s) (.dual a)))).map
        (Q.ginzburgDualOriginalProjectiveMap k φ (Q.source a,s))
        (((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientComponentEquiv Q
          (Q.source a,s) (-1)
          (Q.height (Q.ginzburgPrefixGeneratorEndpoint (Q.source a,s) (.dual a)))).symm
          (Pi.single ⟨.dual a,rfl,rfl⟩ ((Q.unrolledJacobianZAlgebra k φ).id
            (Q.height (Q.ginzburgPrefixGeneratorEndpoint (Q.source a,s) (.dual a)))))))
      ⟨.original b,hb,rfl⟩)=
      Q.ginzburgPrefixCoefficientFixedUnrolledEquiv k φ
        (Q.ginzburgPrefixGeneratorEndpoint (Q.source a,s) (.dual a)) (Q.source a,s) (.original b)
        (Submodule.Quotient.mk (Q.ginzburgUnitHessianComponent k φ a b s)) := by
  rw [Q.ginzburgDualOriginalProjectiveMap_unit_basis k φ (Q.source a,s)
    ⟨.dual a,rfl,rfl⟩]
  change Q.ginzburgPrefixTopFixedUnrolledEquiv k φ
    (Q.ginzburgPrefixGeneratorEndpoint (Q.source a,s) (.dual a)) (Q.source a,s) 0
    (Submodule.Quotient.mk
      ((Q.ginzburgOriginalFilteredToPrefix k φ (Q.target a) (Q.source a)
        (s-(s-(GinzburgArrow.dual a).cutDegree Q))).f 0
        (Q.ginzburgDualLayerDifferential k φ (Q.target a) (Q.source a)
          (s-(s-(GinzburgArrow.dual a).cutDegree Q))
          (Q.ginzburgGeneratorUnitRepresentative k (Q.source a,s) (-1)
            ⟨.dual a,rfl,rfl⟩)))) ⟨.original b,hb,rfl⟩=_
  rw [Q.ginzburgPrefixTopFixedUnrolledEquiv_mk_apply]
  congr 1
  congr 1
  apply Subtype.ext
  rw [Q.ginzburgGeneratorPrefixTopEquiv_apply_coe,
    Q.ginzburgUnitDualHessianPrefix_eq k φ a b s hb]

end ASGinzburg.CutQuiver
