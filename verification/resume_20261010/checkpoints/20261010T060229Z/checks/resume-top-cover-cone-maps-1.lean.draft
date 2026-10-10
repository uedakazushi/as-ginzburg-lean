import work.ASGinzburgDraft.GradedOrdinaryFourTermTopCover
import work.ASGinzburgDraft.GradedOrdinaryBinaryProductMaps
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! Genuine coordinate identities for the cone of a homogeneous lift
from the cover of the top cokernel. -/
namespace ASGinzburg.GradedOrdinaryModuleData
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]
variable {A : ℤ → Submodule k R}
variable (P₁ P₂ P₃ V : GradedOrdinaryModuleData k R A)

theorem topCoverConeIncoming_comp_fst (f₁ : P₁.ringModule ⟶ P₂.ringModule) :
    P₁.topCoverConeIncoming P₂ V f₁ ≫ P₂.binaryProductFst V = f₁ := by
  rw [topCoverConeIncoming,Category.assoc,P₂.binaryProductInl_comp_fst V,Category.comp_id]

theorem binaryProductInl_comp_topCoverConeOutgoing
    (f₂ : P₂.ringModule ⟶ P₃.ringModule) (l : V.ringModule ⟶ P₃.ringModule) :
    P₂.binaryProductInl V ≫ P₂.topCoverConeOutgoing P₃ V f₂ l = f₂ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change f₂ x + l 0 = f₂ x
  rw [map_zero,add_zero]

theorem binaryProductInr_comp_topCoverConeOutgoing
    (f₂ : P₂.ringModule ⟶ P₃.ringModule) (l : V.ringModule ⟶ P₃.ringModule) :
    P₂.binaryProductInr V ≫ P₂.topCoverConeOutgoing P₃ V f₂ l = l := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change f₂ 0 + l x = l x
  rw [map_zero,zero_add]

theorem topCoverConeOutgoing_comp_topProjection
    (f₂ : P₂.ringModule ⟶ P₃.ringModule) (l : V.ringModule ⟶ P₃.ringModule)
    {U : ModuleCat.{v} R} (q : P₃.ringModule ⟶ U) (hq : f₂ ≫ q = 0) :
    P₂.topCoverConeOutgoing P₃ V f₂ l ≫ q = P₂.binaryProductSnd V ≫ (l ≫ q) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change q (f₂ x.1 + l x.2) = q (l x.2)
  rw [map_add]
  have h := congrArg (fun f : P₂.ringModule ⟶ U => f x.1) hq
  change q (f₂ x.1) = 0 at h
  rw [h,zero_add]

end ASGinzburg.GradedOrdinaryModuleData
