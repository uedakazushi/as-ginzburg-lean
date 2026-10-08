import ASGinzburg.LeftModuleExtNaturalSequence
import ASGinzburg.LeftModuleADual
import ASGinzburg.RightModuleHomology

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)
/-- A genuine right module of actual Ext components, with no added duality assumption. -/
noncomputable def leftModuleExtRight (M : A.LeftModule) (n : ℕ) : A.RightModule :=
  ⟨A.leftRepresentableFunctor ⋙ A.leftModuleExtCovariant M n, ⟨inferInstance, inferInstance⟩⟩

@[simp] theorem leftModuleExtRight_obj (M : A.LeftModule) (n : ℕ) (i : ℤ) :
    (A.leftModuleExtRight M n).obj.obj (op ⟨i⟩) =
      ModuleCat.of k (Abelian.Ext.{v} M (A.leftRepresentable i) n) := rfl

/-- Degree zero is naturally the previously constructed A-dual, including its right action. -/
noncomputable def leftModuleExtRightZeroIso (M : A.LeftModule) :
    A.leftModuleExtRight M 0 ≅ A.leftModuleADual M := by
  let e : (A.leftModuleExtRight M 0).obj ≅ (A.leftModuleADual M).obj :=
    NatIso.ofComponents (fun X =>
      (A.leftModuleExtZeroLinearEquiv M (A.leftRepresentable X.unop.index)).toModuleIso) (by
        intro X Y f
        apply ModuleCat.hom_ext
        ext x
        apply (A.leftModuleExtZeroLinearEquiv M (A.leftRepresentable Y.unop.index)).symm.injective
        change (A.leftModuleExtZeroLinearEquiv M (A.leftRepresentable Y.unop.index)).symm
          ((A.leftModuleExtZeroLinearEquiv M (A.leftRepresentable Y.unop.index))
            (x.comp (Abelian.Ext.mk₀ (A.leftRepresentableFunctor.map f)) (by rfl))) =
          (A.leftModuleExtZeroLinearEquiv M (A.leftRepresentable Y.unop.index)).symm
            (A.leftModuleExtZeroLinearEquiv M (A.leftRepresentable X.unop.index) x ≫
              A.leftRepresentableFunctor.map f)
        simp only [LinearEquiv.symm_apply_apply]
        change x.comp (Abelian.Ext.mk₀ (A.leftRepresentableFunctor.map f)) (by rfl) =
          Abelian.Ext.mk₀
            (A.leftModuleExtZeroLinearEquiv M (A.leftRepresentable X.unop.index) x ≫
              A.leftRepresentableFunctor.map f)
        rw [← Abelian.Ext.mk₀_comp_mk₀]
        congr 1
        exact (Abelian.Ext.mk₀_addEquiv₀_apply x).symm)
  exact ⟨e.hom, e.inv, e.hom_inv_id, e.inv_hom_id⟩


end ASGinzburg.ZAlgebra

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

noncomputable def leftModuleExtBoundaryRight {S : ShortComplex A.LeftModule}
    (hS : S.ShortExact) (n : ℕ) :
    A.leftModuleExtRight S.X₁ n ⟶ A.leftModuleExtRight S.X₃ (n+1) :=
  CategoryTheory.Functor.whiskerLeft A.leftRepresentableFunctor (A.leftModuleExtBoundaryNat hS n)

noncomputable instance leftModuleExtBoundaryRightEpi {S : ShortComplex A.LeftModule}
    (hS : S.ShortExact) [Projective S.X₂] (n : ℕ) : Epi (A.leftModuleExtBoundaryRight hS n) := by
  apply (A.rightModule_epi_iff _).mpr
  intro i
  exact inferInstanceAs (Epi ((A.leftModuleExtBoundaryNat hS n).app (A.leftRepresentable i)))

noncomputable def leftModuleExtDimensionShiftRightIso {S : ShortComplex A.LeftModule}
    (hS : S.ShortExact) [Projective S.X₂] (n : ℕ) :
    A.leftModuleExtRight S.X₁ (n+1) ≅ A.leftModuleExtRight S.X₃ (n+2) :=
  A.rightModuleProperty.isoMk
    (CategoryTheory.Functor.isoWhiskerLeft A.leftRepresentableFunctor
      (A.leftModuleExtDimensionShiftNatIso hS n))

theorem leftModuleExtDimensionShiftRightIso_hom {S : ShortComplex A.LeftModule}
    (hS : S.ShortExact) [Projective S.X₂] (n : ℕ) :
    (A.leftModuleExtDimensionShiftRightIso hS n).hom = A.leftModuleExtBoundaryRight hS (n+1) := rfl
noncomputable def leftModuleExtPrecompRight {M N : A.LeftModule} (f : M ⟶ N) (n : ℕ) :
    A.leftModuleExtRight N n ⟶ A.leftModuleExtRight M n :=
  CategoryTheory.Functor.whiskerLeft A.leftRepresentableFunctor (A.leftModuleExtPrecompNat f n)

theorem leftModuleExtPrecompRight_boundary_zero {S : ShortComplex A.LeftModule}
    (hS : S.ShortExact) (n : ℕ) :
    A.leftModuleExtPrecompRight S.f n ≫ A.leftModuleExtBoundaryRight hS n = 0 := by
  apply NatTrans.ext
  funext X
  exact NatTrans.congr_app (A.leftModuleExtPrecompNat_boundary_zero hS n) (A.leftRepresentable X.unop.index)

theorem leftModuleADualMap_extRightZeroIso_inv {M N : A.LeftModule} (f : M ⟶ N) :
    A.leftModuleADualMap f ≫ (A.leftModuleExtRightZeroIso M).inv =
      (A.leftModuleExtRightZeroIso N).inv ≫ A.leftModuleExtPrecompRight f 0 := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change Abelian.Ext.mk₀ (f ≫ x) =
    (Abelian.Ext.mk₀ f).comp (Abelian.Ext.mk₀ x) (Nat.zero_add 0)
  exact (Abelian.Ext.mk₀_comp_mk₀ _ _).symm
theorem leftModuleExtBoundaryRight_exact {S : ShortComplex A.LeftModule}
    (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk (A.leftModuleExtPrecompRight S.f n) (A.leftModuleExtBoundaryRight hS n)
      (A.leftModuleExtPrecompRight_boundary_zero hS n)).Exact := by
  apply (A.rightModule_exact_iff _).mpr
  intro i
  exact A.leftModuleExtBoundaryShortComplex_exact_component hS (A.leftRepresentable i) n
end ASGinzburg.ZAlgebra
