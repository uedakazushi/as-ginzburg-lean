import work.ASGinzburgDraft.BalancedTensorBifunctor
import ASGinzburg.BalancedTensorTor

/-! A genuine isomorphism of ordinary right modules induces a natural
isomorphism of their actual second-factor derived balanced tensors. -/
namespace ASGinzburg
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable {M M' : ModuleCat.{max v w} Rᵐᵒᵖ}

noncomputable def balancedTensorTorFirstObjectIso (e : M ≅ M') (n : ℕ) :
    balancedTensorTorFunctor.{u,v,max v w,z} k R M n ≅
      balancedTensorTorFunctor.{u,v,max v w,z} k R M' n := by
  let d : balancedTensorRightFunctor.{u,v,max v w,max v w z} k R M ≅
      balancedTensorRightFunctor.{u,v,max v w,max v w z} k R M' :=
    (balancedTensorBifunctor.{u,v,max v w,max v w z} k R).mapIso e
  exact
    { hom := NatTrans.leftDerived d.hom n
      inv := NatTrans.leftDerived d.inv n
      hom_inv_id := by
        rw [← NatTrans.leftDerived_comp, d.hom_inv_id, NatTrans.leftDerived_id]
        rfl
      inv_hom_id := by
        rw [← NatTrans.leftDerived_comp, d.inv_hom_id, NatTrans.leftDerived_id]
        rfl }

end ASGinzburg
