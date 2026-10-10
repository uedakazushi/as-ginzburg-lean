import ASGinzburg.AlgebraEnvelopingRegularModule
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! The enveloping algebra of the opposite ring is genuinely isomorphic
to the original enveloping algebra by exchanging its two tensor factors.
Unop identifies the actual multiplication modules after this restriction. -/
namespace ASGinzburg
open CategoryTheory
open scoped TensorProduct
universe u v
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]

noncomputable def algebraEnvelopingOppositeAlgEquiv :
    AlgebraEnvelopingRing k Rᵐᵒᵖ ≃ₐ[k] AlgebraEnvelopingRing k R :=
  (Algebra.TensorProduct.comm k Rᵐᵒᵖ Rᵐᵒᵖᵐᵒᵖ).trans
    (Algebra.TensorProduct.congr (AlgEquiv.opOp k R).symm (AlgEquiv.refl : Rᵐᵒᵖ ≃ₐ[k] Rᵐᵒᵖ))

@[simp] theorem algebraEnvelopingOppositeAlgEquiv_tmul (a b : R) :
    algebraEnvelopingOppositeAlgEquiv k R
      (MulOpposite.op a ⊗ₜ[k] MulOpposite.op (MulOpposite.op b)) =
      b ⊗ₜ[k] MulOpposite.op a := by
  simp only [algebraEnvelopingOppositeAlgEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul]
  rfl

noncomputable def regularEnvelopingOppositeRestrictionEquiv :
    regularEnvelopingModuleCat k Rᵐᵒᵖ ≃ₗ[AlgebraEnvelopingRing k Rᵐᵒᵖ]
      (ModuleCat.restrictScalars (algebraEnvelopingOppositeAlgEquiv k R).toRingEquiv.toRingHom).obj
        (regularEnvelopingModuleCat k R) where
  toFun := MulOpposite.unop
  invFun := MulOpposite.op
  left_inv := MulOpposite.op_unop
  right_inv := MulOpposite.unop_op
  map_add' := MulOpposite.unop_add
  map_smul' t x := by
    let y : Rᵐᵒᵖ := x
    change (regularEnvelopingRepresentation k Rᵐᵒᵖ t y).unop =
      regularEnvelopingRepresentation k R (algebraEnvelopingOppositeAlgEquiv k R t)
        y.unop
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
        change (regularEnvelopingRepresentation k Rᵐᵒᵖ
          (MulOpposite.op a.unop ⊗ₜ[k] MulOpposite.op (MulOpposite.op b.unop.unop))
          y).unop =
          regularEnvelopingRepresentation k R (algebraEnvelopingOppositeAlgEquiv k R
            (MulOpposite.op a.unop ⊗ₜ[k] MulOpposite.op (MulOpposite.op b.unop.unop)))
              y.unop
        rw [regularEnvelopingRepresentation_tmul, algebraEnvelopingOppositeAlgEquiv_tmul,
          regularEnvelopingRepresentation_tmul]
        exact (mul_assoc b.unop.unop y.unop a.unop).symm
    | add t s ht hs =>
        simp only [map_add, LinearMap.add_apply, MulOpposite.unop_add, ht, hs]

noncomputable def regularEnvelopingOppositeRestrictionIso :
    regularEnvelopingModuleCat k Rᵐᵒᵖ ≅
      (ModuleCat.restrictScalars (algebraEnvelopingOppositeAlgEquiv k R).toRingEquiv.toRingHom).obj
        (regularEnvelopingModuleCat k R) :=
  (regularEnvelopingOppositeRestrictionEquiv k R).toModuleIso

end ASGinzburg
