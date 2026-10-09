import ASGinzburg.GinzburgProjectiveYonedaEntries

/-! Actual path Hessians and original arrows supply Jacobian matrix
entries indexed by the unchanged native incoming generator families. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgGeneratorHessianEntry (φ : Q.Potential k)
    (v : Q.LiftVertex) (a : Q.GinzburgIncomingDegree v.1 (-1))
    (b : Q.GinzburgIncomingDegree v.1 0) :
    (Q.unrolledJacobianZAlgebra k φ).Hom
      (Q.height (Q.ginzburgPrefixGeneratorEndpoint v a.val))
      (Q.height (Q.ginzburgPrefixGeneratorEndpoint v b.val)) := by
  rcases v with ⟨v,s⟩
  obtain ⟨a,ha,hda⟩ := a
  cases a with
  | original a => norm_num [GinzburgArrow.cohomologicalDegree] at hda
  | loop w => norm_num [GinzburgArrow.cohomologicalDegree] at hda
  | dual a =>
    change Q.source a=v at ha
    subst v
    obtain ⟨b,hb,hdb⟩ := b
    cases b with
    | dual b => norm_num [GinzburgArrow.cohomologicalDegree] at hdb
    | loop w => norm_num [GinzburgArrow.cohomologicalDegree] at hdb
    | original b =>
      exact Q.ginzburgPrefixCoefficientFixedUnrolledEquiv k φ
        (Q.ginzburgPrefixGeneratorEndpoint (Q.source a,s) (.dual a)) (Q.source a,s) (.original b)
        (Submodule.Quotient.mk (Q.ginzburgUnitHessianComponent k φ a b s))

noncomputable def ginzburgGeneratorLoopArrowEntry (φ : Q.Potential k)
    (v : Q.LiftVertex) (b : Q.GinzburgIncomingDegree v.1 (-1)) :
    (Q.unrolledJacobianZAlgebra k φ).Hom
      (Q.height (Q.ginzburgPrefixGeneratorEndpoint v (.loop v.1)))
      (Q.height (Q.ginzburgPrefixGeneratorEndpoint v b.val)) := by
  obtain ⟨b,hb,hdb⟩ := b
  cases b with
  | original b => norm_num [GinzburgArrow.cohomologicalDegree] at hdb
  | loop w => norm_num [GinzburgArrow.cohomologicalDegree] at hdb
  | dual b =>
    exact Q.ginzburgPrefixCoefficientFixedUnrolledEquiv k φ
      (Q.ginzburgPrefixGeneratorEndpoint v (.loop v.1)) v (.dual b)
      (Submodule.Quotient.mk (Q.ginzburgUnitLoopTopArrowComponent k v.1 v.2 b hb))

theorem ginzburgDualOriginalProjectiveMap_yoneda_entry (φ : Q.Potential k)
    (v : Q.LiftVertex) (a : Q.GinzburgIncomingDegree v.1 (-1))
    (b : Q.GinzburgIncomingDegree v.1 0) :
    (Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientComponentEquiv Q v 0
      (Q.height (Q.ginzburgPrefixGeneratorEndpoint v a.val))
      ((Q.unrolledJacobianZAlgebra k φ).representableYonedaEquiv
        (Q.height (Q.ginzburgPrefixGeneratorEndpoint v a.val))
        ((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientModule Q v 0)
        (Sigma.ι (fun c : Q.GinzburgIncomingDegree v.1 (-1) =>
          (Q.unrolledJacobianZAlgebra k φ).representable
            (Q.height (Q.ginzburgPrefixGeneratorEndpoint v c.val))) a ≫
          Q.ginzburgDualOriginalProjectiveMap k φ v)) b=
      Q.ginzburgGeneratorHessianEntry k φ v a b := by
  rcases v with ⟨v,s⟩
  obtain ⟨a,ha,hda⟩ := a
  cases a with
  | original a => norm_num [GinzburgArrow.cohomologicalDegree] at hda
  | loop w => norm_num [GinzburgArrow.cohomologicalDegree] at hda
  | dual a =>
    change Q.source a=v at ha
    subst v
    obtain ⟨b,hb,hdb⟩ := b
    cases b with
    | dual b => norm_num [GinzburgArrow.cohomologicalDegree] at hdb
    | loop w => norm_num [GinzburgArrow.cohomologicalDegree] at hdb
    | original b =>
      exact Q.ginzburgDualOriginalProjectiveMap_yoneda_hessian k φ a b s hb

theorem ginzburgLoopDualProjectiveMap_yoneda_entry (φ : Q.Potential k)
    (v : Q.LiftVertex) (b : Q.GinzburgIncomingDegree v.1 (-1)) :
    (Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientComponentEquiv Q v (-1)
      (Q.height (Q.ginzburgPrefixGeneratorEndpoint v (.loop v.1)))
      ((Q.unrolledJacobianZAlgebra k φ).representableYonedaEquiv
        (Q.height (Q.ginzburgPrefixGeneratorEndpoint v (.loop v.1)))
        ((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientModule Q v (-1))
        (Sigma.ι (fun c : Q.GinzburgIncomingDegree v.1 (-2) =>
          (Q.unrolledJacobianZAlgebra k φ).representable
            (Q.height (Q.ginzburgPrefixGeneratorEndpoint v c.val)))
          ⟨.loop v.1,rfl,rfl⟩ ≫ Q.ginzburgLoopDualProjectiveMap k φ v)) b=
      Q.ginzburgGeneratorLoopArrowEntry k φ v b := by
  rcases v with ⟨v,s⟩
  obtain ⟨b,hb,hdb⟩ := b
  cases b with
  | original b => norm_num [GinzburgArrow.cohomologicalDegree] at hdb
  | loop w => norm_num [GinzburgArrow.cohomologicalDegree] at hdb
  | dual b => exact Q.ginzburgLoopDualProjectiveMap_yoneda_arrow k φ v s b hb

end ASGinzburg.CutQuiver
