import work.ASGinzburgDraft.AlgebraEnvelopingQuotient
import ASGinzburg.AlgebraEnvelopingTensorRegularFree
import ASGinzburg.AlgebraEnvelopingTensorBifunctor
import ASGinzburg.ScalarQuotientVertexDecomposition
import ASGinzburg.AlgebraModuleRestrictionComparison

/-! The tensor of the actual ordinary quotient modules has the genuine
right enveloping quotient action. All field actions on bundled modules
are compared with their canonical quotient actions explicitly. -/
namespace ASGinzburg
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u v
set_option maxHeartbeats 800000
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (J : Ideal R) [J.IsTwoSided]

noncomputable def quotientEnvelopingRightTargetModule :
    Module (AlgebraEnvelopingRing k R)ᵐᵒᵖ
      (AlgebraEnvelopingRing k (R ⧸ J))ᵐᵒᵖ :=
  Module.compHom _ (algebraEnvelopingQuotientAugmentation k R J).toRingHom.op

attribute [local instance] quotientEnvelopingRightTargetModule

noncomputable def quotientEnvelopingRightTargetObject :
    ModuleCat.{v} (AlgebraEnvelopingRing k R)ᵐᵒᵖ :=
  ModuleCat.of _ (AlgebraEnvelopingRing k (R ⧸ J))ᵐᵒᵖ

def idealQuotientRightScalarTower : IsScalarTower k Rᵐᵒᵖ (R ⧸ J)ᵐᵒᵖ := by
  apply IsScalarTower.of_algebraMap_smul
  intro c x
  change (Ideal.Quotient.mkₐ k J).op (algebraMap k Rᵐᵒᵖ c) * x = c • x
  rw [AlgHom.commutes, Algebra.smul_def]

attribute [local instance] idealQuotientRightScalarTower

abbrev QuotientTensorRightSpace :=
  @TensorProduct k _ (R ⧸ J)ᵐᵒᵖ (R ⧸ J) _ _
    (Module.compHom (R ⧸ J)ᵐᵒᵖ (algebraMap k Rᵐᵒᵖ))
    (Module.compHom (R ⧸ J) (algebraMap k R))

noncomputable def quotientTensorRightCanonicalFieldEquiv :
    QuotientTensorRightSpace k R J ≃ₗ[k]
      (AlgebraEnvelopingRing k (R ⧸ J))ᵐᵒᵖ :=
  (TensorProduct.congr
    (algebraModuleRestrictScalarsIso k Rᵐᵒᵖ (R ⧸ J)ᵐᵒᵖ).toLinearEquiv
    (algebraModuleRestrictScalarsIso k R (R ⧸ J)).toLinearEquiv).trans
      ((TensorProduct.congr (MulOpposite.opLinearEquiv k).symm
        (LinearEquiv.refl k (R ⧸ J))).trans
          (tensorRightEnvelopingRegularLinearEquiv k (R ⧸ J)))

noncomputable def quotientTensorRightTmul (s : (R ⧸ J)ᵐᵒᵖ) (t : R ⧸ J) :
    QuotientTensorRightSpace k R J :=
  @TensorProduct.tmul k _ (R ⧸ J)ᵐᵒᵖ (R ⧸ J) _ _
    (Module.compHom (R ⧸ J)ᵐᵒᵖ (algebraMap k Rᵐᵒᵖ))
    (Module.compHom (R ⧸ J) (algebraMap k R)) s t

theorem quotientTensorRightCanonicalFieldEquiv_tmul
    (s : (R ⧸ J)ᵐᵒᵖ) (t : R ⧸ J) :
    quotientTensorRightCanonicalFieldEquiv k R J (quotientTensorRightTmul k R J s t) =
      MulOpposite.op (s.unop ⊗ₜ[k] MulOpposite.op t) := by
  simp only [quotientTensorRightTmul, quotientTensorRightCanonicalFieldEquiv,
    LinearEquiv.trans_apply]
  rfl

noncomputable def quotientTensorRightSourceObject :
    ModuleCat.{v} (AlgebraEnvelopingRing k R)ᵐᵒᵖ :=
  (((tensorRightEnvelopingBifunctor k R).obj (idealQuotientRightObject J)).obj
    (ModuleCat.of R (R ⧸ J)))

noncomputable def quotientTensorRightEnvelopingEquiv :
    (quotientTensorRightSourceObject k R J) ≃ₗ[(AlgebraEnvelopingRing k R)ᵐᵒᵖ]
      (quotientEnvelopingRightTargetObject k R J) where
  toFun := quotientTensorRightCanonicalFieldEquiv k R J
  invFun := (quotientTensorRightCanonicalFieldEquiv k R J).symm
  left_inv := (quotientTensorRightCanonicalFieldEquiv k R J).left_inv
  right_inv := (quotientTensorRightCanonicalFieldEquiv k R J).right_inv
  map_add' x y := (quotientTensorRightCanonicalFieldEquiv k R J).map_add x y
  map_smul' e x := by
    change quotientTensorRightCanonicalFieldEquiv k R J (e • x) =
      (algebraEnvelopingQuotientAugmentation k R J).op e *
        quotientTensorRightCanonicalFieldEquiv k R J x
    obtain ⟨e, rfl⟩ := MulOpposite.op_surjective e
    induction e using TensorProduct.induction_on with
    | zero => simp only [MulOpposite.op_zero, zero_smul, map_zero, zero_mul]
    | tmul a b =>
        induction x using TensorProduct.induction_on with
        | zero => simp only [smul_zero, map_zero, mul_zero]
        | tmul s t =>
            rw [tensorRightEnvelopingModule_tmul_smul]
            rw [quotientTensorRightCanonicalFieldEquiv_tmul,
              quotientTensorRightCanonicalFieldEquiv_tmul]
            change MulOpposite.op
              ((s.unop * Ideal.Quotient.mk J a) ⊗ₜ[k]
                MulOpposite.op (Ideal.Quotient.mk J b.unop * t)) =
              MulOpposite.op (algebraEnvelopingQuotientAugmentation k R J
                (a ⊗ₜ[k] b)) * MulOpposite.op (s.unop ⊗ₜ[k] MulOpposite.op t)
            rw [← MulOpposite.op_mul]
            rw [algebraEnvelopingQuotientAugmentation_tmul,
              Algebra.TensorProduct.tmul_mul_tmul]
            rfl
        | add x y hx hy => simp only [smul_add, map_add, hx, hy, mul_add]
    | add e f he hf =>
        simp only [MulOpposite.op_add, add_smul, map_add, he, hf, add_mul]

end ASGinzburg
