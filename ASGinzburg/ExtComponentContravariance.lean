import ASGinzburg.RightModuleExtLeftSequence
import ASGinzburg.LeftModuleExtRightSequence

namespace ASGinzburg
open CategoryTheory Opposite
universe u v w
variable {k : Type w} [Semiring k] (C : Type u) [Category.{v} C]
  [Preadditive C] [Linear k C]

def oppositeLinear : Linear k Cᵒᵖ where
  homModule _ _ :=
    { smul := fun r f => (r • f.unop).op
      smul_add := fun r f g => Quiver.Hom.unop_inj (smul_add r f.unop g.unop)
      add_smul := fun r s f => Quiver.Hom.unop_inj (add_smul r s f.unop)
      one_smul := fun f => Quiver.Hom.unop_inj (one_smul k f.unop)
      mul_smul := fun r s f => Quiver.Hom.unop_inj (mul_smul r s f.unop)
      zero_smul := fun f => Quiver.Hom.unop_inj (zero_smul k f.unop)
      smul_zero := fun r => Quiver.Hom.unop_inj (smul_zero r) }
  smul_comp X Y Z r f g :=
    Quiver.Hom.unop_inj (Linear.comp_smul Z.unop Y.unop X.unop g.unop r f.unop)
  comp_smul X Y Z f r g :=
    Quiver.Hom.unop_inj (Linear.smul_comp Z.unop Y.unop X.unop r g.unop f.unop)
end ASGinzburg

namespace ASGinzburg.ZAlgebra
open CategoryTheory Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)
instance rightModuleOppositeLinear : Linear k A.RightModuleᵒᵖ := ASGinzburg.oppositeLinear _
instance leftModuleOppositeLinear : Linear k A.LeftModuleᵒᵖ := ASGinzburg.oppositeLinear _
end ASGinzburg.ZAlgebra

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

noncomputable def rightModuleExtLeftFunctor (n : ℕ) : A.RightModuleᵒᵖ ⥤ A.LeftModule where
  obj M := A.rightModuleExtLeft M.unop n
  map f := A.rightModuleExtPrecompLeft f.unop n
  map_id M := by
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    ext e
    exact e.mk₀_id_comp
  map_comp f g := by
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    ext e
    change (Abelian.Ext.mk₀ (g.unop ≫ f.unop)).comp e (zero_add n) =
      (Abelian.Ext.mk₀ g.unop).comp ((Abelian.Ext.mk₀ f.unop).comp e (zero_add n)) (zero_add n)
    rw [← Abelian.Ext.mk₀_comp_mk₀]
    apply Abelian.Ext.comp_assoc
    omega

instance rightModuleExtLeftFunctorAdditive (n : ℕ) : (A.rightModuleExtLeftFunctor n).Additive where
  map_add := by
    intro X Y f g
    apply NatTrans.ext
    funext Z
    apply ModuleCat.hom_ext
    ext e
    change (Abelian.Ext.mk₀ (f.unop + g.unop)).comp e (zero_add n) =
      (Abelian.Ext.mk₀ f.unop).comp e (zero_add n) +
        (Abelian.Ext.mk₀ g.unop).comp e (zero_add n)
    rw [Abelian.Ext.mk₀_add, Abelian.Ext.add_comp]

instance rightModuleExtLeftFunctorLinear (n : ℕ) : (A.rightModuleExtLeftFunctor n).Linear k where
  map_smul := by
    intro X Y f r
    apply NatTrans.ext
    funext Z
    apply ModuleCat.hom_ext
    ext e
    change (Abelian.Ext.mk₀ (r • f.unop)).comp e (zero_add n) =
      r • (Abelian.Ext.mk₀ f.unop).comp e (zero_add n)
    rw [A.rightModuleExt_mk₀_smul]
    exact A.rightModuleExt_smul_comp _ _ _ r
end ASGinzburg.ZAlgebra

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

noncomputable def leftModuleExtRightFunctor (n : ℕ) : A.LeftModuleᵒᵖ ⥤ A.RightModule where
  obj M := A.leftModuleExtRight M.unop n
  map f := A.leftModuleExtPrecompRight f.unop n
  map_id M := by
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    ext e
    exact e.mk₀_id_comp
  map_comp f g := by
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    ext e
    change (Abelian.Ext.mk₀ (g.unop ≫ f.unop)).comp e (zero_add n) =
      (Abelian.Ext.mk₀ g.unop).comp ((Abelian.Ext.mk₀ f.unop).comp e (zero_add n)) (zero_add n)
    rw [← Abelian.Ext.mk₀_comp_mk₀]
    apply Abelian.Ext.comp_assoc
    omega

instance leftModuleExtRightFunctorAdditive (n : ℕ) : (A.leftModuleExtRightFunctor n).Additive where
  map_add := by
    intro X Y f g
    apply NatTrans.ext
    funext Z
    apply ModuleCat.hom_ext
    ext e
    change (Abelian.Ext.mk₀ (f.unop + g.unop)).comp e (zero_add n) =
      (Abelian.Ext.mk₀ f.unop).comp e (zero_add n) +
        (Abelian.Ext.mk₀ g.unop).comp e (zero_add n)
    rw [Abelian.Ext.mk₀_add, Abelian.Ext.add_comp]

instance leftModuleExtRightFunctorLinear (n : ℕ) : (A.leftModuleExtRightFunctor n).Linear k where
  map_smul := by
    intro X Y f r
    apply NatTrans.ext
    funext Z
    apply ModuleCat.hom_ext
    ext e
    change (Abelian.Ext.mk₀ (r • f.unop)).comp e (zero_add n) =
      r • (Abelian.Ext.mk₀ f.unop).comp e (zero_add n)
    rw [A.leftModuleExt_mk₀_smul]
    exact A.leftModuleExt_smul_comp _ _ _ r
end ASGinzburg.ZAlgebra
