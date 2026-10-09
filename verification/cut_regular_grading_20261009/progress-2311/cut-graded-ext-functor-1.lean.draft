import ASGinzburg.PeriodCutGradedModuleExt

/-! Actual derived Ext on graded right R modules is an additive
ModuleCat-valued functor in the second variable. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable {Q : CutQuiver} {E : A.PeriodIso (Q.vertices:ℤ)}

theorem cutGradedExt_smul_comp {X Y Z : E.CutGradedRightModule Q} {a b c : ℕ}
    (x : Abelian.Ext.{v} X Y a) (y : Abelian.Ext.{v} Y Z b) (h : a+b=c) (r : k) :
    (r • x).comp y h=r • x.comp y h := by
  letI := HasDerivedCategory.standard (E.CutGradedRightModule Q)
  apply (ASGinzburg.exactExtHomLinearEquiv k X Z c).injective
  rw [LinearEquiv.map_smul]
  change ((r • x).comp y h).hom=r • (x.comp y h).hom
  rw [Abelian.Ext.comp_hom,Abelian.Ext.comp_hom]
  have hx : (r • x).hom=r • x.hom :=
    (ASGinzburg.exactExtHomLinearEquiv k X Y a).map_smul r x
  rw [hx]
  dsimp only [ShiftedHom.comp,ZAlgebra.shiftedHomModule]
  exact Linear.smul_comp _ _ _ r x.hom _

noncomputable def cutGradedExtPostcomp {M N P : E.CutGradedRightModule Q}
    (f : N⟶P) (n : ℕ) : Abelian.Ext.{v} M N n →ₗ[k] Abelian.Ext.{v} M P n where
  toFun x := x.comp (Abelian.Ext.mk₀ f) (Nat.add_zero n)
  map_add' x y := Abelian.Ext.add_comp x y _ _
  map_smul' r x := cutGradedExt_smul_comp x _ _ r

noncomputable def cutGradedExtCovariant (M : E.CutGradedRightModule Q) (n : ℕ) :
    E.CutGradedRightModule Q ⥤ ModuleCat.{v} k where
  obj N := ModuleCat.of k (Abelian.Ext.{v} M N n)
  map f := ModuleCat.ofHom (cutGradedExtPostcomp f n)
  map_id N := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Abelian.Ext.comp_mk₀_id x
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change x.comp (Abelian.Ext.mk₀ (f≫g)) (Nat.add_zero n)=
      (x.comp (Abelian.Ext.mk₀ f) (Nat.add_zero n)).comp
        (Abelian.Ext.mk₀ g) (Nat.add_zero n)
    rw [← Abelian.Ext.mk₀_comp_mk₀]
    symm
    apply Abelian.Ext.comp_assoc
    omega

instance cutGradedExtCovariantAdditive (M : E.CutGradedRightModule Q) (n : ℕ) :
    (cutGradedExtCovariant M n).Additive where
  map_add := by
    intro X Y f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change x.comp (Abelian.Ext.mk₀ (f+g)) (Nat.add_zero n)=
      x.comp (Abelian.Ext.mk₀ f) (Nat.add_zero n)+x.comp (Abelian.Ext.mk₀ g) (Nat.add_zero n)
    rw [Abelian.Ext.mk₀_add,Abelian.Ext.comp_add]

end ASGinzburg.ZAlgebra.PeriodIso
