import work.ASGinzburgDraft.GradedOrdinaryBinaryProduct
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! The canonical product maps and their genuine images under an
additive functor satisfy the actual coordinate identities. -/
namespace ASGinzburg.GradedOrdinaryModuleData
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v w
variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]
variable {A : ℤ → Submodule k R}
variable (M N : GradedOrdinaryModuleData k R A)

theorem binaryProductInl_comp_fst : M.binaryProductInl N ≫ M.binaryProductFst N = 𝟙 _ := by
  apply ModuleCat.hom_ext
  rfl

theorem binaryProductInl_comp_snd : M.binaryProductInl N ≫ M.binaryProductSnd N = 0 := by
  apply ModuleCat.hom_ext
  rfl

theorem binaryProductInr_comp_fst : M.binaryProductInr N ≫ M.binaryProductFst N = 0 := by
  apply ModuleCat.hom_ext
  rfl

theorem binaryProductInr_comp_snd : M.binaryProductInr N ≫ M.binaryProductSnd N = 𝟙 _ := by
  apply ModuleCat.hom_ext
  rfl

theorem binaryProduct_coordinates :
    M.binaryProductFst N ≫ M.binaryProductInl N +
      M.binaryProductSnd N ≫ M.binaryProductInr N = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (x.1,0) + (0,x.2) = x
  exact Prod.ext (add_zero x.1) (zero_add x.2)

theorem binaryProductFunctor_coordinates {S : Type w} [Ring S]
    (F : ModuleCat.{v} R ⥤ ModuleCat.{w} S) [F.Additive]
    (x : F.obj (M.binaryProductData N).ringModule) :
    F.map (M.binaryProductInl N) (F.map (M.binaryProductFst N) x) +
      F.map (M.binaryProductInr N) (F.map (M.binaryProductSnd N) x) = x := by
  have h := congrArg (fun f => F.map f) (M.binaryProduct_coordinates N)
  dsimp only at h
  rw [F.map_add,F.map_comp,F.map_comp,F.map_id] at h
  exact congrArg (fun f : F.obj (M.binaryProductData N).ringModule ⟶
    F.obj (M.binaryProductData N).ringModule => f x) h

end ASGinzburg.GradedOrdinaryModuleData
