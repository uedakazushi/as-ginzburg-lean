import ASGinzburg.GradedOrdinaryRingDualComponentMaps

/-! The actual raw ordinary ring dual and actual categorical Hom into
the regular module have the same field-linear structure. -/
namespace ASGinzburg
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]

noncomputable def ordinaryRingDualHomFieldEquiv (P : ModuleCat.{v} R) :
    ordinaryRingDual R P ≃ₗ[k] (P ⟶ ModuleCat.of R R) where
  toFun := ModuleCat.ofHom
  invFun := ModuleCat.Hom.hom
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ordinaryRingDual_field_smul_apply P c f x

 theorem ordinaryRingDualHomFieldEquiv_precomp {P Q : ModuleCat.{v} R}
    (a : P ⟶ Q) (f : ordinaryRingDual R Q) :
    ordinaryRingDualHomFieldEquiv k R P (ordinaryRingDualMap R a f) =
      a ≫ ordinaryRingDualHomFieldEquiv k R Q f := rfl

end ASGinzburg
