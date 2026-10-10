import ASGinzburg.PeriodCutGradedExtFunctor

/-! Actual Ext postcomposition is linear also in the second factor,
using the proved k-linear structure of the actual derived category. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable {Q : CutQuiver} {E : A.PeriodIso (Q.vertices:ℤ)}

noncomputable instance cutGradedDerivedSingleLinear (a : ℤ) :
    letI := HasDerivedCategory.standard (E.CutGradedRightModule Q)
    (DerivedCategory.singleFunctor (E.CutGradedRightModule Q) a).Linear k := by
  letI := HasDerivedCategory.standard (E.CutGradedRightModule Q)
  exact inferInstanceAs ((HomotopyCategory.singleFunctor (E.CutGradedRightModule Q) a ⋙
    (DerivedCategory.Qh : _ ⥤ DerivedCategory (E.CutGradedRightModule Q))).Linear k)

theorem cutGradedExt_mk₀_smul {M N : E.CutGradedRightModule Q} (r : k) (f : M⟶N) :
    Abelian.Ext.mk₀ (r • f)=r • (Abelian.Ext.mk₀ f : Abelian.Ext.{v} M N 0) := by
  letI := HasDerivedCategory.standard (E.CutGradedRightModule Q)
  apply (ASGinzburg.exactExtHomLinearEquiv k M N 0).injective
  rw [LinearEquiv.map_smul]
  change (Abelian.Ext.mk₀ (r • f)).hom=r • (Abelian.Ext.mk₀ f).hom
  rw [Abelian.Ext.mk₀_hom,Abelian.Ext.mk₀_hom]
  dsimp only [ShiftedHom.mk₀]
  rw [Functor.map_smul]
  change (r • (DerivedCategory.singleFunctor (E.CutGradedRightModule Q) 0).map f) ≫ _=
    r • ((DerivedCategory.singleFunctor (E.CutGradedRightModule Q) 0).map f ≫ _)
  rw [Linear.smul_comp]

theorem cutGradedExt_comp_smul {X Y Z : E.CutGradedRightModule Q} {a b c : ℕ}
    (x : Abelian.Ext.{v} X Y a) (y : Abelian.Ext.{v} Y Z b) (h : a+b=c) (r : k) :
    x.comp (r • y) h=r • x.comp y h := by
  letI := HasDerivedCategory.standard (E.CutGradedRightModule Q)
  apply (ASGinzburg.exactExtHomLinearEquiv k X Z c).injective
  rw [LinearEquiv.map_smul]
  change (x.comp (r • y) h).hom=r • (x.comp y h).hom
  rw [Abelian.Ext.comp_hom,Abelian.Ext.comp_hom]
  have hy : (r • y).hom=r • y.hom :=
    (ASGinzburg.exactExtHomLinearEquiv k Y Z b).map_smul r y
  rw [hy]
  dsimp only [ShiftedHom.comp,ZAlgebra.shiftedHomModule]
  rw [Functor.map_smul,Linear.smul_comp,Linear.comp_smul]

end ASGinzburg.ZAlgebra.PeriodIso
