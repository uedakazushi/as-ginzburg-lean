import ASGinzburg.RegularLeftModule
import ASGinzburg.RegularExtComparison

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

noncomputable def leftLocallyUnitalExtIso {M N P : A.LeftLocallyUnitalModule}
    (e : N ≅ P) (n : ℕ) : Abelian.Ext.{v} M N n ≃ₗ[k] Abelian.Ext.{v} M P n := by
  letI := HasDerivedCategory.standard A.LeftLocallyUnitalModule
  exact ASGinzburg.exactExtPostcompIso k e n

theorem leftLocallyUnitalExtIso_conjugation {M N P : A.LeftLocallyUnitalModule}
    (e : N ≅ P) (n : ℕ) (f : N ⟶ N) (x : Abelian.Ext.{v} M N n) :
    A.leftLocallyUnitalExtIso e n (x.comp (Abelian.Ext.mk₀ f) (Nat.add_zero n)) =
      (A.leftLocallyUnitalExtIso e n x).comp
        (Abelian.Ext.mk₀ (e.inv ≫ f ≫ e.hom)) (Nat.add_zero n) := by
  letI := HasDerivedCategory.standard A.LeftLocallyUnitalModule
  exact ASGinzburg.exactExtPostcompIso_conjugation k e n f x

noncomputable def leftRegularExtGrLinearEquiv (M : A.LeftModule) (n : ℕ) :
    Abelian.Ext.{v} M A.leftRegularCoproduct n ≃ₗ[k]
      Abelian.Ext.{v} (A.leftTotalLocallyUnitalModule M) A.totalAlgebraLeftLocallyUnitalModule n :=
  (A.leftLocallyUnitalExtLinearEquiv M A.leftRegularCoproduct n).trans
    (A.leftLocallyUnitalExtIso A.leftRegularTotalLocallyUnitalIso n)

theorem leftRegularExtGrLinearEquiv_postcomp (M : A.LeftModule) (n : ℕ)
    (f : A.leftRegularCoproduct ⟶ A.leftRegularCoproduct)
    (x : Abelian.Ext.{v} M A.leftRegularCoproduct n) :
    A.leftRegularExtGrLinearEquiv M n (x.comp (Abelian.Ext.mk₀ f) (Nat.add_zero n)) =
      (A.leftRegularExtGrLinearEquiv M n x).comp
        (Abelian.Ext.mk₀ (A.leftRegularTotalLocallyUnitalIso.inv ≫
          A.leftTotalLocallyUnitalFunctor.map f ≫ A.leftRegularTotalLocallyUnitalIso.hom))
          (Nat.add_zero n) := by
  change A.leftLocallyUnitalExtIso A.leftRegularTotalLocallyUnitalIso n
    (A.leftLocallyUnitalExtLinearEquiv M A.leftRegularCoproduct n
      (x.comp (Abelian.Ext.mk₀ f) (Nat.add_zero n))) = _
  rw [A.leftLocallyUnitalExtLinearEquiv_postcomp]
  exact A.leftLocallyUnitalExtIso_conjugation A.leftRegularTotalLocallyUnitalIso n _ _

end ASGinzburg.ZAlgebra
