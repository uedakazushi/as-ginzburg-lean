import ASGinzburg.RightModuleExt
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.Algebra.Module.TransferInstance

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

/-- ShiftedHom inherits the actual scalar action on morphisms of a linear category. -/
instance shiftedHomModule {C : Type*} [Category C] [Preadditive C] [Linear k C]
    [HasShift C ℤ] (X Y : C) (n : ℤ) : Module k (ShiftedHom X Y n) := by
  dsimp only [ShiftedHom]
  infer_instance

/-- The standard derived category is k-linear by the universal localization construction. -/
noncomputable instance rightModuleDerivedLinear :
    letI := HasDerivedCategory.standard A.RightModule
    Linear k (DerivedCategory A.RightModule) := by
  letI := HasDerivedCategory.standard A.RightModule
  exact Localization.linear k (DerivedCategory.Qh : _ ⥤ DerivedCategory A.RightModule)
    (HomotopyCategory.quasiIso A.RightModule _)

/-- The standard localization from the homotopy category respects the existing k action. -/
noncomputable instance rightModuleDerivedQhLinear :
    letI := HasDerivedCategory.standard A.RightModule
    letI : Linear k (DerivedCategory A.RightModule) := A.rightModuleDerivedLinear
    (DerivedCategory.Qh : _ ⥤ DerivedCategory A.RightModule).Linear k := by
  letI := HasDerivedCategory.standard A.RightModule
  letI : Linear k (DerivedCategory A.RightModule) := A.rightModuleDerivedLinear
  exact Localization.functor_linear k _ (HomotopyCategory.quasiIso A.RightModule _)

noncomputable instance rightModuleDerivedSingleLinear (n : ℤ) :
    letI := HasDerivedCategory.standard A.RightModule
    letI : Linear k (DerivedCategory A.RightModule) := A.rightModuleDerivedLinear
    (DerivedCategory.singleFunctor A.RightModule n).Linear k := by
  letI := HasDerivedCategory.standard A.RightModule
  letI : Linear k (DerivedCategory A.RightModule) := A.rightModuleDerivedLinear
  letI := A.rightModuleDerivedQhLinear
  exact inferInstanceAs (Functor.Linear k (HomotopyCategory.singleFunctor A.RightModule n ⋙
    (DerivedCategory.Qh : _ ⥤ DerivedCategory A.RightModule)))

noncomputable def rightModuleExtHomAddEquiv (M N : A.RightModule) (n : ℕ) :
    Abelian.Ext.{v} M N n ≃+
      (letI := HasDerivedCategory.standard A.RightModule
       letI : Linear k (DerivedCategory A.RightModule) := A.rightModuleDerivedLinear
       ShiftedHom ((DerivedCategory.singleFunctor A.RightModule 0).obj M)
         ((DerivedCategory.singleFunctor A.RightModule 0).obj N) (n : ℤ)) := by
  letI := HasDerivedCategory.standard A.RightModule
  exact Abelian.Ext.homAddEquiv

noncomputable instance rightModuleExtModule (M N : A.RightModule) (n : ℕ) :
    Module k (Abelian.Ext.{v} M N n) := by
  letI := HasDerivedCategory.standard A.RightModule
  letI : Linear k (DerivedCategory A.RightModule) := A.rightModuleDerivedLinear
  exact (A.rightModuleExtHomAddEquiv M N n).module k

noncomputable def rightModuleExtHomLinearEquiv (M N : A.RightModule) (n : ℕ) :
    Abelian.Ext.{v} M N n ≃ₗ[k]
      (letI := HasDerivedCategory.standard A.RightModule
       letI : Linear k (DerivedCategory A.RightModule) := A.rightModuleDerivedLinear
       ShiftedHom ((DerivedCategory.singleFunctor A.RightModule 0).obj M)
         ((DerivedCategory.singleFunctor A.RightModule 0).obj N) (n : ℤ)) := by
  letI := HasDerivedCategory.standard A.RightModule
  letI : Linear k (DerivedCategory A.RightModule) := A.rightModuleDerivedLinear
  exact {
    A.rightModuleExtHomAddEquiv M N n with
    map_smul' := by
      intro r x
      exact (A.rightModuleExtHomAddEquiv M N n).apply_symm_apply _ }

/-- The transported scalar action agrees with the original scalar action on degree-zero Hom. -/
theorem rightModuleExt_mk₀_smul {M N : A.RightModule} (r : k) (f : M ⟶ N) :
    Abelian.Ext.mk₀ (r • f) = r • (Abelian.Ext.mk₀ f : Abelian.Ext.{v} M N 0) := by
  letI := HasDerivedCategory.standard A.RightModule
  letI : Linear k (DerivedCategory A.RightModule) := A.rightModuleDerivedLinear
  letI := A.rightModuleDerivedQhLinear
  letI := A.rightModuleDerivedSingleLinear 0
  apply (A.rightModuleExtHomLinearEquiv M N 0).injective
  rw [LinearEquiv.map_smul]
  change (Abelian.Ext.mk₀ (r • f)).hom = r • (Abelian.Ext.mk₀ f).hom
  rw [Abelian.Ext.mk₀_hom, Abelian.Ext.mk₀_hom]
  dsimp only [ShiftedHom.mk₀]
  rw [Functor.map_smul]
  change (r • (DerivedCategory.singleFunctor A.RightModule 0).map f) ≫ _ =
    r • ((DerivedCategory.singleFunctor A.RightModule 0).map f ≫ _)
  simp only [Linear.smul_comp]

noncomputable def rightModuleExtZeroLinearEquiv (M N : A.RightModule) :
    Abelian.Ext.{v} M N 0 ≃ₗ[k] (M ⟶ N) where
  toAddEquiv := Abelian.Ext.addEquiv₀
  map_smul' r x := by
    apply (Abelian.Ext.addEquiv₀ (X := M) (Y := N)).symm.injective
    change Abelian.Ext.mk₀ (Abelian.Ext.homEquiv₀ (r • x)) =
      Abelian.Ext.mk₀ (r • Abelian.Ext.homEquiv₀ x)
    rw [Abelian.Ext.mk₀_homEquiv₀_apply, A.rightModuleExt_mk₀_smul,
      Abelian.Ext.mk₀_homEquiv₀_apply]

noncomputable def representableExtZeroLinearEquiv (i : ℤ) (M : A.RightModule) :
    Abelian.Ext.{v} (A.representable i) M 0 ≃ₗ[k] (A.rightModuleEvaluation i).obj M :=
  (A.rightModuleExtZeroLinearEquiv _ _).trans (A.representableYonedaEquiv i M)

end ASGinzburg.ZAlgebra
