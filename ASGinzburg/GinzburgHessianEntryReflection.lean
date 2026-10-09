import ASGinzburg.GinzburgHessianOppositeClasses

/-! The unchanged native projective Hessian Jacobian matrix itself
transposes under the actual reflected opposite algebra isomorphism. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgHessianOppositeArrowIncidence (a b : Q.Arrow)
    (hb : Q.target b=Q.source a) : Q.opposite.target a=Q.opposite.source b := by
  change (Q.source a).rev=(Q.target b).rev
  rw [hb]

theorem ginzburgGeneratorHessianEntry_opposite_raw (φ : Q.Potential k)
    (a b : Q.Arrow) (s : ℤ) (hb : Q.target b=Q.source a) :
    (Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).homTransport
      _ _ _ _
      (congrArg Q.opposite.height (Q.ginzburgHessianOppositeSource a b s))
      (congrArg Q.opposite.height (Q.ginzburgHessianOppositeTarget a b s))
      (Q.oppositeUnrolledJacobianHomEquiv k φ
        (Q.ginzburgPrefixGeneratorEndpoint (Q.source a,s) (.dual a))
        (Q.ginzburgPrefixGeneratorEndpoint (Q.source a,s) (.original b))
        (Q.ginzburgGeneratorHessianEntry k φ (Q.source a,s)
          ⟨.dual a,rfl,rfl⟩ ⟨.original b,hb,rfl⟩))=
      Q.opposite.ginzburgGeneratorHessianEntry k (Q.oppositePotentialEquiv k φ)
        (Q.opposite.source b,1-s) ⟨.dual b,rfl,rfl⟩
          ⟨.original a,Q.ginzburgHessianOppositeArrowIncidence a b hb,rfl⟩ := by
  rw [Q.ginzburgGeneratorHessianEntry_pathClass k φ a b s hb,
    Q.opposite.ginzburgGeneratorHessianEntry_pathClass k (Q.oppositePotentialEquiv k φ)
      b a (1-s) (Q.ginzburgHessianOppositeArrowIncidence a b hb)]
  exact Q.ginzburgHessianPathClass_opposite k φ a b s

end ASGinzburg.CutQuiver
