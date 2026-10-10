import work.ASGinzburgDraft.SplitQuotientRingDualCoordinates

/-! The split quotient dual identification uses the actual canonical
field action of its bundled right quotient module. -/
namespace ASGinzburg
open scoped ModuleCat.Algebra
universe u v w
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (J : Ideal R) [J.IsTwoSided]
variable (I : Type w) [Fintype I] [DecidableEq I]
variable (e : (R ⧸ J) ≃ₐ[k] (I → k))
attribute [local instance] idealQuotientRightScalarTower

noncomputable def splitQuotientCanonicalDualFieldChange :
    BalancedTensorHom k R (idealQuotientRightObject J) k ≃ₗ[k]
      BalancedTensorHom k R (R ⧸ J)ᵐᵒᵖ k :=
  (balancedTensorHomLinearEquiv k R (idealQuotientRightObject J) k).trans
    (((idealQuotientRightCanonicalFieldIso k R J).toLinearEquiv.symm.dualMap).trans
      (balancedTensorHomLinearEquiv k R (R ⧸ J)ᵐᵒᵖ k).symm)

@[simp] theorem splitQuotientCanonicalDualFieldChange_apply
    (φ : BalancedTensorHom k R (idealQuotientRightObject J) k)
    (x : (R ⧸ J)ᵐᵒᵖ) :
    splitQuotientCanonicalDualFieldChange k R J φ x = φ x := rfl

theorem splitQuotientCanonicalDualFieldChange_action (r : R)
    (φ : BalancedTensorHom k R (idealQuotientRightObject J) k) :
    splitQuotientCanonicalDualFieldChange k R J (r • φ) =
      r • splitQuotientCanonicalDualFieldChange k R J φ := by
  ext x
  rfl

noncomputable def splitQuotientCanonicalDualLeftLinearEquiv :
    BalancedTensorHom k R (idealQuotientRightObject J) k ≃ₗ[R] (R ⧸ J) := by
  let f := (splitQuotientCanonicalDualFieldChange k R J).trans
    (splitQuotientDualFieldEquiv k R J I e)
  exact {
    toFun := f
    invFun := f.symm
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_add' := f.map_add
    map_smul' := fun r φ => by
      change splitQuotientDualFieldEquiv k R J I e
          (splitQuotientCanonicalDualFieldChange k R J (r • φ)) =
        r • splitQuotientDualFieldEquiv k R J I e
          (splitQuotientCanonicalDualFieldChange k R J φ)
      rw [splitQuotientCanonicalDualFieldChange_action,
        splitQuotientDualFieldEquiv_action] }

end ASGinzburg
