import ASGinzburg.EnvelopingBalancedTensorRightMaps
import ASGinzburg.AlgebraEnvelopingRestrictedRegular
import ASGinzburg.BalancedTensorRightUnit

/-! The actual right-module-valued balanced tensor functor sends the
regular multiplication bimodule R to the original right module M. -/
namespace ASGinzburg
open scoped ModuleCat.Algebra TensorProduct
universe u v w
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module Rᵐᵒᵖ M]
variable [IsScalarTower k Rᵐᵒᵖ M]

noncomputable def envelopingBalancedTensorRegularFieldEquiv :
    EnvelopingBalancedTensorSpace k R M (regularEnvelopingModuleCat k R) ≃ₗ[k] M := by
  let P := regularEnvelopingModuleCat k R
  letI := envelopingLeftModule k R P
  letI := envelopingLeftScalarTower k R P
  let eR : P ≃ₗ[R] R := {
    toFun := id
    invFun := id
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun a x => by
      letI := regularEnvelopingModule k R
      change (a ⊗ₜ[k] (1 : Rᵐᵒᵖ)) • (show R from x)=a*(show R from x)
      simpa only [MulOpposite.op_one,mul_one] using
        regularEnvelopingModule_tmul_smul k R a 1 x}
  let eT : BalancedTensorSpace k R M P ≃ₗ[k] BalancedTensorSpace k R M R := {
    toFun := balancedTensorMapRight k R M eR.toLinearMap
    invFun := balancedTensorMapRight k R M eR.symm.toLinearMap
    left_inv := fun t => by
      change (balancedTensorMapRight k R M eR.symm.toLinearMap).comp
        (balancedTensorMapRight k R M eR.toLinearMap) t=t
      have h : eR.symm.toLinearMap.comp eR.toLinearMap=LinearMap.id := by
        apply LinearMap.ext
        intro x
        exact eR.symm_apply_apply x
      rw [← balancedTensorMapRight_comp,h,balancedTensorMapRight_id]
      rfl
    right_inv := fun t => by
      change (balancedTensorMapRight k R M eR.toLinearMap).comp
        (balancedTensorMapRight k R M eR.symm.toLinearMap) t=t
      have h : eR.toLinearMap.comp eR.symm.toLinearMap=LinearMap.id := by
        apply LinearMap.ext
        intro x
        exact eR.apply_symm_apply x
      rw [← balancedTensorMapRight_comp,h,balancedTensorMapRight_id]
      rfl
    map_add' := map_add _
    map_smul' := map_smul _}
  exact eT.trans (balancedTensorRightUnitEquiv k R M)

theorem envelopingBalancedTensorRegularFieldEquiv_tmul (x : M)
    (r : regularEnvelopingModuleCat k R) :
    letI := envelopingLeftModule k R (regularEnvelopingModuleCat k R)
    envelopingBalancedTensorRegularFieldEquiv k R M
      (balancedTensorTmul k R M (regularEnvelopingModuleCat k R) x r)=
        MulOpposite.op (show R from r) • x := by
  letI := envelopingLeftModule k R (regularEnvelopingModuleCat k R)
  letI := envelopingLeftScalarTower k R (regularEnvelopingModuleCat k R)
  unfold envelopingBalancedTensorRegularFieldEquiv
  rw [LinearEquiv.trans_apply]
  change balancedTensorRightUnitMap k R M
    (balancedTensorMapRight k R M _ (balancedTensorTmul k R M _ x r))=MulOpposite.op (show R from r) • x
  rw [balancedTensorMapRight_tmul,balancedTensorRightUnitMap_tmul]
  rfl

noncomputable def envelopingBalancedTensorRegularRightEquiv :
    letI := envelopingBalancedTensorRightModule k R M (regularEnvelopingModuleCat k R)
    EnvelopingBalancedTensorSpace k R M (regularEnvelopingModuleCat k R) ≃ₗ[Rᵐᵒᵖ] M := by
  let P := regularEnvelopingModuleCat k R
  letI := envelopingLeftModule k R P
  letI := envelopingRightModule k R P
  letI := envelopingBalancedTensorRightModule k R M P
  let e := envelopingBalancedTensorRegularFieldEquiv k R M
  exact {
    toFun := e
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv
    map_add' := e.map_add
    map_smul' := fun b t => by
      refine balancedTensorSpace_induction k R M P (fun t => e (b • t)=b • e t) ?_ ?_ ?_ t
      · simp only [smul_zero,map_zero]
      · intro x r
        rw [envelopingBalancedTensorRightModule_tmul]
        change envelopingBalancedTensorRegularFieldEquiv k R M (balancedTensorTmul k R M P x (b • r))=
          b • envelopingBalancedTensorRegularFieldEquiv k R M (balancedTensorTmul k R M P x r)
        rw [envelopingBalancedTensorRegularFieldEquiv_tmul,envelopingBalancedTensorRegularFieldEquiv_tmul]
        have hr : (show R from b • r)=(show R from r)*b.unop := by
          letI := regularEnvelopingModule k R
          change ((1 : R) ⊗ₜ[k] b) • (show R from r)=(show R from r)*b.unop
          simpa only [one_mul] using regularEnvelopingModule_tmul_smul k R 1 b.unop (show R from r)
        rw [hr,MulOpposite.op_mul,mul_smul,MulOpposite.op_unop]
      · intro a c ha hc
        simp only [smul_add,map_add,ha,hc]}

end ASGinzburg
