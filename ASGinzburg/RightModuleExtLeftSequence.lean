import ASGinzburg.LeftModuleHomology
import ASGinzburg.RightModuleExtNaturalSequence

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

noncomputable def rightModuleExtBoundaryLeft {S : ShortComplex A.RightModule}
    (hS : S.ShortExact) (n : ℕ) :
    A.rightModuleExtLeft S.X₁ n ⟶ A.rightModuleExtLeft S.X₃ (n+1) :=
  CategoryTheory.Functor.whiskerLeft A.representableFunctor (A.rightModuleExtBoundaryNat hS n)

noncomputable instance rightModuleExtBoundaryLeftEpi {S : ShortComplex A.RightModule}
    (hS : S.ShortExact) [Projective S.X₂] (n : ℕ) : Epi (A.rightModuleExtBoundaryLeft hS n) := by
  apply (A.leftModule_epi_iff _).mpr
  intro i
  exact inferInstanceAs (Epi ((A.rightModuleExtBoundaryNat hS n).app (A.representable i)))

noncomputable def rightModuleExtDimensionShiftLeftIso {S : ShortComplex A.RightModule}
    (hS : S.ShortExact) [Projective S.X₂] (n : ℕ) :
    A.rightModuleExtLeft S.X₁ (n+1) ≅ A.rightModuleExtLeft S.X₃ (n+2) :=
  A.leftModuleProperty.isoMk
    (CategoryTheory.Functor.isoWhiskerLeft A.representableFunctor
      (A.rightModuleExtDimensionShiftNatIso hS n))

theorem rightModuleExtDimensionShiftLeftIso_hom {S : ShortComplex A.RightModule}
    (hS : S.ShortExact) [Projective S.X₂] (n : ℕ) :
    (A.rightModuleExtDimensionShiftLeftIso hS n).hom = A.rightModuleExtBoundaryLeft hS (n+1) := rfl
noncomputable def rightModuleExtPrecompLeft {M N : A.RightModule} (f : M ⟶ N) (n : ℕ) :
    A.rightModuleExtLeft N n ⟶ A.rightModuleExtLeft M n :=
  CategoryTheory.Functor.whiskerLeft A.representableFunctor (A.rightModuleExtPrecompNat f n)

theorem rightModuleExtPrecompLeft_boundary_zero {S : ShortComplex A.RightModule}
    (hS : S.ShortExact) (n : ℕ) :
    A.rightModuleExtPrecompLeft S.f n ≫ A.rightModuleExtBoundaryLeft hS n = 0 := by
  apply NatTrans.ext
  funext X
  exact NatTrans.congr_app (A.rightModuleExtPrecompNat_boundary_zero hS n) (A.representable X.index)

theorem rightModuleADualMap_extLeftZeroIso_inv {M N : A.RightModule} (f : M ⟶ N) :
    A.rightModuleADualMap f ≫ (A.rightModuleExtLeftZeroIso M).inv =
      (A.rightModuleExtLeftZeroIso N).inv ≫ A.rightModuleExtPrecompLeft f 0 := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change Abelian.Ext.mk₀ (f ≫ x) =
    (Abelian.Ext.mk₀ f).comp (Abelian.Ext.mk₀ x) (Nat.zero_add 0)
  exact (Abelian.Ext.mk₀_comp_mk₀ _ _).symm
theorem rightModuleExtBoundaryLeft_exact {S : ShortComplex A.RightModule}
    (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk (A.rightModuleExtPrecompLeft S.f n) (A.rightModuleExtBoundaryLeft hS n)
      (A.rightModuleExtPrecompLeft_boundary_zero hS n)).Exact := by
  apply (A.leftModule_exact_iff _).mpr
  intro i
  exact A.rightModuleExtBoundaryShortComplex_exact_component hS (A.representable i) n
end ASGinzburg.ZAlgebra
