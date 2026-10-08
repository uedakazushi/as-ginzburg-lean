import ASGinzburg.LeftModuleExtSequence

/-! Natural connecting maps and shifts for the actual derived-category Ext. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

noncomputable def leftModuleExtPrecomp {M N : A.LeftModule} (f : M ⟶ N)
    (P : A.LeftModule) (n : ℕ) :
    Abelian.Ext.{v} N P n →ₗ[k] Abelian.Ext.{v} M P n where
  toFun x := (Abelian.Ext.mk₀ f).comp x (Nat.zero_add n)
  map_add' x y := Abelian.Ext.comp_add _ x y _
  map_smul' r x := A.leftModuleExt_comp_smul _ x _ r

noncomputable def leftModuleExtPrecompNat {M N : A.LeftModule} (f : M ⟶ N)
    (n : ℕ) : A.leftModuleExtCovariant N n ⟶ A.leftModuleExtCovariant M n where
  app P := ModuleCat.ofHom (A.leftModuleExtPrecomp f P n)
  naturality := by
    intro X Y g
    apply ModuleCat.hom_ext
    ext x
    change (Abelian.Ext.mk₀ f).comp (x.comp (Abelian.Ext.mk₀ g) (Nat.add_zero n))
      (Nat.zero_add n) = ((Abelian.Ext.mk₀ f).comp x (Nat.zero_add n)).comp
        (Abelian.Ext.mk₀ g) (Nat.add_zero n)
    symm
    apply Abelian.Ext.comp_assoc
    omega

noncomputable def leftModuleExtBoundaryNat {S : ShortComplex A.LeftModule}
    (hS : S.ShortExact) (n : ℕ) :
    A.leftModuleExtCovariant S.X₁ n ⟶ A.leftModuleExtCovariant S.X₃ (n + 1) where
  app N := ModuleCat.ofHom (A.leftModuleExtBoundary hS N n)
  naturality := by
    intro X Y f
    apply ModuleCat.hom_ext
    ext x
    change hS.extClass.comp (x.comp (Abelian.Ext.mk₀ f) (Nat.add_zero n))
      (Nat.add_comm 1 n) = (hS.extClass.comp x (Nat.add_comm 1 n)).comp
        (Abelian.Ext.mk₀ f) (Nat.add_zero (n + 1))
    symm
    apply Abelian.Ext.comp_assoc
    omega

noncomputable def leftModuleExtDimensionShiftNatIso {S : ShortComplex A.LeftModule}
    (hS : S.ShortExact) [Projective S.X₂] (n : ℕ) :
    A.leftModuleExtCovariant S.X₁ (n + 1) ≅ A.leftModuleExtCovariant S.X₃ (n + 2) :=
  NatIso.ofComponents (fun N => (A.leftModuleExtDimensionShift hS N n).toModuleIso)
    (by intro X Y f; exact (A.leftModuleExtBoundaryNat hS (n + 1)).naturality f)

theorem leftModuleExtPrecompNat_boundary_zero {S : ShortComplex A.LeftModule}
    (hS : S.ShortExact) (n : ℕ) :
    A.leftModuleExtPrecompNat S.f n ≫ A.leftModuleExtBoundaryNat hS n = 0 := by
  apply NatTrans.ext
  funext N
  apply ModuleCat.hom_ext
  ext x
  change hS.extClass.comp ((Abelian.Ext.mk₀ S.f).comp x (Nat.zero_add n))
    (Nat.add_comm 1 n) = 0
  rw [← Abelian.Ext.comp_assoc_of_second_deg_zero, hS.extClass_comp, Abelian.Ext.zero_comp]

noncomputable def leftModuleExtBoundaryShortComplex {S : ShortComplex A.LeftModule}
    (hS : S.ShortExact) (n : ℕ) : ShortComplex (A.LeftModule ⥤ ModuleCat.{v} k) :=
  ShortComplex.mk (A.leftModuleExtPrecompNat S.f n) (A.leftModuleExtBoundaryNat hS n)
    (A.leftModuleExtPrecompNat_boundary_zero hS n)

theorem leftModuleExtBoundaryShortComplex_exact_component {S : ShortComplex A.LeftModule}
    (hS : S.ShortExact) (N : A.LeftModule) (n : ℕ) :
    ((A.leftModuleExtBoundaryShortComplex hS n).map
      ((evaluation A.LeftModule (ModuleCat.{v} k)).obj N)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  exact Abelian.Ext.contravariant_sequence_exact₁ hS N x (Nat.add_comm 1 n) hx

noncomputable instance leftModuleExtBoundaryNatAppEpi {S : ShortComplex A.LeftModule}
    (hS : S.ShortExact) [Projective S.X₂] (N : A.LeftModule) (n : ℕ) :
    Epi ((A.leftModuleExtBoundaryNat hS n).app N) := by
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro x
  exact Abelian.Ext.contravariant_sequence_exact₃ hS N x
    (Abelian.Ext.eq_zero_of_projective _) (Nat.add_comm 1 n)

noncomputable instance leftModuleExtBoundaryNatEpi {S : ShortComplex A.LeftModule}
    (hS : S.ShortExact) [Projective S.X₂] (n : ℕ) :
    Epi (A.leftModuleExtBoundaryNat hS n) := NatTrans.epi_of_epi_app _

/-- A functor-category cokernel is obtained from the actual long exact sequence. -/
noncomputable def leftModuleExtBoundaryCoforkIsColimit {S : ShortComplex A.LeftModule}
    (hS : S.ShortExact) [Projective S.X₂] (n : ℕ) :
    IsColimit (CokernelCofork.ofπ (A.leftModuleExtBoundaryNat hS n)
      (A.leftModuleExtPrecompNat_boundary_zero hS n)) := by
  apply evaluationJointlyReflectsColimits
  intro N
  refine (isColimitMapCoconeCoforkEquiv'
    ((evaluation A.LeftModule (ModuleCat.{v} k)).obj N)
    (A.leftModuleExtPrecompNat_boundary_zero hS n)).symm ?_
  letI : Epi ((A.leftModuleExtBoundaryShortComplex hS n).map
      ((evaluation A.LeftModule (ModuleCat.{v} k)).obj N)).g := by
    change Epi ((A.leftModuleExtBoundaryNat hS n).app N)
    infer_instance
  exact (A.leftModuleExtBoundaryShortComplex_exact_component hS N n).gIsCokernel

/-- Natural presentation of actual Ext by a cokernel, without Hom vanishing. -/
noncomputable def leftModuleExtCokernelNatIso {S : ShortComplex A.LeftModule}
    (hS : S.ShortExact) [Projective S.X₂] (n : ℕ) :
    cokernel (A.leftModuleExtPrecompNat S.f n) ≅ A.leftModuleExtCovariant S.X₃ (n + 1) :=
  IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _)
    (A.leftModuleExtBoundaryCoforkIsColimit hS n)

@[reassoc] theorem leftModuleExtCokernelNatIso_π_hom {S : ShortComplex A.LeftModule}
    (hS : S.ShortExact) [Projective S.X₂] (n : ℕ) :
    cokernel.π (A.leftModuleExtPrecompNat S.f n) ≫
        (A.leftModuleExtCokernelNatIso hS n).hom = A.leftModuleExtBoundaryNat hS n :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel _)
    (A.leftModuleExtBoundaryCoforkIsColimit hS n) .one

end ASGinzburg.ZAlgebra
