import ASGinzburg.ExtClassNaturality
import ASGinzburg.ProjectiveResolutionSyzygyNaturality
import ASGinzburg.RightResolutionDuality
import ASGinzburg.LeftResolutionDuality

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

theorem rightModuleExtBoundaryLeft_natural {S T : ShortComplex A.RightModule}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) (n : ℕ) :
    A.rightModuleExtPrecompLeft φ.τ₁ n ≫ A.rightModuleExtBoundaryLeft hS n =
      A.rightModuleExtBoundaryLeft hT n ≫ A.rightModuleExtPrecompLeft φ.τ₃ (n+1) := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro e
  exact ASGinzburg.extBoundary_natural hS hT φ (A.representable X.index) n e

theorem rightResolutionExtTopProjection_natural {M N : A.RightModule}
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
    (hP₄ : IsZero (P.complex.X 4)) (hQ₄ : IsZero (Q.complex.X 4))
    (F : P.complex ⟶ Q.complex) (f : M ⟶ N)
    (hπ : F.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f) :
    A.rightModuleADualMap (F.f 3) ≫ A.rightResolutionExtTopProjection P hP₄ =
      A.rightResolutionExtTopProjection Q hQ₄ ≫ A.rightModuleExtPrecompLeft f 3 := by
  have H₂ := A.rightModuleExtBoundaryLeft_natural (P.shortExact₂ hP₄) (Q.shortExact₂ hQ₄)
    (P.shortExact₂Hom Q F f hπ) 0
  have H₁ := A.rightModuleExtBoundaryLeft_natural P.shortExact₁ Q.shortExact₁
    (P.shortExact₁Hom Q F f hπ) 1
  have H₀ := A.rightModuleExtBoundaryLeft_natural P.shortExact₀ Q.shortExact₀
    (P.shortExact₀Hom Q F f hπ) 2
  change A.rightModuleExtPrecompLeft (F.f 3) 0 ≫ A.rightModuleExtBoundaryLeft (P.shortExact₂ hP₄) 0 =
    A.rightModuleExtBoundaryLeft (Q.shortExact₂ hQ₄) 0 ≫
      A.rightModuleExtPrecompLeft (P.secondKernelMap Q F f hπ) 1 at H₂
  change A.rightModuleExtPrecompLeft (P.secondKernelMap Q F f hπ) 1 ≫
      A.rightModuleExtBoundaryLeft P.shortExact₁ 1 =
    A.rightModuleExtBoundaryLeft Q.shortExact₁ 1 ≫
      A.rightModuleExtPrecompLeft (P.firstKernelMap Q F f hπ) 2 at H₁
  change A.rightModuleExtPrecompLeft (P.firstKernelMap Q F f hπ) 2 ≫
      A.rightModuleExtBoundaryLeft P.shortExact₀ 2 =
    A.rightModuleExtBoundaryLeft Q.shortExact₀ 2 ≫ A.rightModuleExtPrecompLeft f 3 at H₀
  dsimp only [rightResolutionExtTopProjection]
  simp only [rightModuleExtDimensionShiftLeftIso_hom]
  rw [← Category.assoc,A.rightModuleADualMap_extLeftZeroIso_inv]
  simp only [Category.assoc]
  rw [← Category.assoc (A.rightModuleExtPrecompLeft (F.f 3) 0),H₂]
  simp only [Category.assoc]
  rw [← Category.assoc (A.rightModuleExtPrecompLeft (P.secondKernelMap Q F f hπ) 1),H₁]
  simp only [Category.assoc]
  rw [H₀]
end ASGinzburg.ZAlgebra

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

theorem leftModuleExtBoundaryRight_natural {S T : ShortComplex A.LeftModule}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) (n : ℕ) :
    A.leftModuleExtPrecompRight φ.τ₁ n ≫ A.leftModuleExtBoundaryRight hS n =
      A.leftModuleExtBoundaryRight hT n ≫ A.leftModuleExtPrecompRight φ.τ₃ (n+1) := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro e
  exact ASGinzburg.extBoundary_natural hS hT φ (A.leftRepresentable X.unop.index) n e

theorem leftResolutionExtTopProjection_natural {M N : A.LeftModule}
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
    (hP₄ : IsZero (P.complex.X 4)) (hQ₄ : IsZero (Q.complex.X 4))
    (F : P.complex ⟶ Q.complex) (f : M ⟶ N)
    (hπ : F.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f) :
    A.leftModuleADualMap (F.f 3) ≫ A.leftResolutionExtTopProjection P hP₄ =
      A.leftResolutionExtTopProjection Q hQ₄ ≫ A.leftModuleExtPrecompRight f 3 := by
  have H₂ := A.leftModuleExtBoundaryRight_natural (P.shortExact₂ hP₄) (Q.shortExact₂ hQ₄)
    (P.shortExact₂Hom Q F f hπ) 0
  have H₁ := A.leftModuleExtBoundaryRight_natural P.shortExact₁ Q.shortExact₁
    (P.shortExact₁Hom Q F f hπ) 1
  have H₀ := A.leftModuleExtBoundaryRight_natural P.shortExact₀ Q.shortExact₀
    (P.shortExact₀Hom Q F f hπ) 2
  change A.leftModuleExtPrecompRight (F.f 3) 0 ≫ A.leftModuleExtBoundaryRight (P.shortExact₂ hP₄) 0 =
    A.leftModuleExtBoundaryRight (Q.shortExact₂ hQ₄) 0 ≫
      A.leftModuleExtPrecompRight (P.secondKernelMap Q F f hπ) 1 at H₂
  change A.leftModuleExtPrecompRight (P.secondKernelMap Q F f hπ) 1 ≫
      A.leftModuleExtBoundaryRight P.shortExact₁ 1 =
    A.leftModuleExtBoundaryRight Q.shortExact₁ 1 ≫
      A.leftModuleExtPrecompRight (P.firstKernelMap Q F f hπ) 2 at H₁
  change A.leftModuleExtPrecompRight (P.firstKernelMap Q F f hπ) 2 ≫
      A.leftModuleExtBoundaryRight P.shortExact₀ 2 =
    A.leftModuleExtBoundaryRight Q.shortExact₀ 2 ≫ A.leftModuleExtPrecompRight f 3 at H₀
  dsimp only [leftResolutionExtTopProjection]
  simp only [leftModuleExtDimensionShiftRightIso_hom]
  rw [← Category.assoc,A.leftModuleADualMap_extRightZeroIso_inv]
  simp only [Category.assoc]
  rw [← Category.assoc (A.leftModuleExtPrecompRight (F.f 3) 0),H₂]
  simp only [Category.assoc]
  rw [← Category.assoc (A.leftModuleExtPrecompRight (P.secondKernelMap Q F f hπ) 1),H₁]
  simp only [Category.assoc]
  rw [H₀]
end ASGinzburg.ZAlgebra
