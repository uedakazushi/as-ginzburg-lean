import ASGinzburg.ASRelationArrowQuotient

/-! The actual I/IJ comparison takes a genuine relation representative
to the previously constructed AS kernel element, not an arbitrary
isomorphism chosen from a dimension count. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)
  (R : ∀ w : Q.LiftVertex, A.ASResolution Q w)

theorem presentationRelationArrowQuotientFirstKernelEquiv_mk
    (u w : Q.LiftVertex) (huw : u≠w)
    (f : LinearMap.ker (A.unrolledPathLinearEvaluation Q R u w)) :
    A.presentationRelationArrowQuotientFirstKernelEquiv Q R u w huw
      (Submodule.Quotient.mk (A.pathRelationHeightEquiv Q R u w f))=
        A.pathRelationsToCategoricalASFirstKernel Q R u w huw f := by
  simp only [presentationRelationArrowQuotientFirstKernelEquiv,LinearEquiv.trans_apply,
    Submodule.Quotient.equiv_symm,Submodule.Quotient.equiv_apply,
    Submodule.mapQ_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,
    pathRelationsFirstKernelEquiv,LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

end ASGinzburg.ZAlgebra
