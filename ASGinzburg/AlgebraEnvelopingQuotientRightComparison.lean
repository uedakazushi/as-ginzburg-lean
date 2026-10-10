import ASGinzburg.AlgebraEnvelopingQuotientTensorRightModule

/-! The actual right module of the enveloping kernel quotient is
isomorphic to the tensor of the ordinary right and left quotients.
All actions are the actual quotient/augmentation actions. -/
namespace ASGinzburg
open CategoryTheory
universe u v
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (J : Ideal R) [J.IsTwoSided]

noncomputable def quotientEnvelopingRightKernelEquiv :
    (idealQuotientRightObject (algebraEnvelopingQuotientKernel k R J))
      ≃ₗ[(AlgebraEnvelopingRing k R)ᵐᵒᵖ]
        (quotientEnvelopingRightTargetObject k R J) where
  toFun x := MulOpposite.op (algebraEnvelopingQuotientAlgEquiv k R J x.unop)
  invFun x := MulOpposite.op ((algebraEnvelopingQuotientAlgEquiv k R J).symm x.unop)
  left_inv x := by
    apply MulOpposite.unop_injective
    exact (algebraEnvelopingQuotientAlgEquiv k R J).symm_apply_apply x.unop
  right_inv x := by
    apply MulOpposite.unop_injective
    exact (algebraEnvelopingQuotientAlgEquiv k R J).apply_symm_apply x.unop
  map_add' x y := by
    exact congrArg MulOpposite.op
      ((algebraEnvelopingQuotientAlgEquiv k R J).map_add x.unop y.unop)
  map_smul' r x := by
    change MulOpposite.op (algebraEnvelopingQuotientAlgEquiv k R J
        (x.unop * Ideal.Quotient.mk (algebraEnvelopingQuotientKernel k R J) r.unop)) =
      (algebraEnvelopingQuotientAugmentation k R J).op r *
        MulOpposite.op (algebraEnvelopingQuotientAlgEquiv k R J x.unop)
    rw [map_mul, algebraEnvelopingQuotientAlgEquiv_mk]
    rfl

noncomputable def quotientEnvelopingRightKernelIso :
    idealQuotientRightObject (algebraEnvelopingQuotientKernel k R J) ≅
      quotientEnvelopingRightTargetObject k R J :=
  (quotientEnvelopingRightKernelEquiv k R J).toModuleIso

noncomputable def quotientTensorRightKernelIso :
    quotientTensorRightSourceObject k R J ≅
      idealQuotientRightObject (algebraEnvelopingQuotientKernel k R J) :=
  (quotientTensorRightEnvelopingEquiv k R J).toModuleIso ≪≫
    (quotientEnvelopingRightKernelIso k R J).symm

end ASGinzburg
