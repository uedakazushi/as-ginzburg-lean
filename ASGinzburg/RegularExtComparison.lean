import ASGinzburg.LinearExtTransport
import ASGinzburg.RegularLeftMultiplication

/-! Actual Ext into the total algebra, compared with the old component Ext
module. The isomorphism intertwines postcomposition by every left multiplier
with the complete total-algebra left action. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

noncomputable def rightLocallyUnitalExtIso {M N P : A.RightLocallyUnitalModule}
    (e : N ≅ P) (n : ℕ) : Abelian.Ext.{v} M N n ≃ₗ[k] Abelian.Ext.{v} M P n := by
  letI := HasDerivedCategory.standard A.RightLocallyUnitalModule
  exact ASGinzburg.exactExtPostcompIso k e n

theorem rightLocallyUnitalExtIso_conjugation {M N P : A.RightLocallyUnitalModule}
    (e : N ≅ P) (n : ℕ) (f : N ⟶ N) (x : Abelian.Ext.{v} M N n) :
    A.rightLocallyUnitalExtIso e n (x.comp (Abelian.Ext.mk₀ f) (Nat.add_zero n)) =
      (A.rightLocallyUnitalExtIso e n x).comp
        (Abelian.Ext.mk₀ (e.inv ≫ f ≫ e.hom)) (Nat.add_zero n) := by
  letI := HasDerivedCategory.standard A.RightLocallyUnitalModule
  exact ASGinzburg.exactExtPostcompIso_conjugation k e n f x

noncomputable def rightRegularExtGrLinearEquiv (M : A.RightModule) (n : ℕ) :
    Abelian.Ext.{v} M A.rightRegularCoproduct n ≃ₗ[k]
      Abelian.Ext.{v} (A.rightTotalLocallyUnitalModule M) A.totalAlgebraRightLocallyUnitalModule n :=
  (A.rightLocallyUnitalExtLinearEquiv M A.rightRegularCoproduct n).trans
    (A.rightLocallyUnitalExtIso A.rightRegularTotalLocallyUnitalIso n)

theorem rightRegularExtGrLinearEquiv_postcomp (M : A.RightModule) (n : ℕ)
    (f : A.rightRegularCoproduct ⟶ A.rightRegularCoproduct)
    (x : Abelian.Ext.{v} M A.rightRegularCoproduct n) :
    A.rightRegularExtGrLinearEquiv M n (x.comp (Abelian.Ext.mk₀ f) (Nat.add_zero n)) =
      (A.rightRegularExtGrLinearEquiv M n x).comp
        (Abelian.Ext.mk₀ (A.rightRegularTotalLocallyUnitalIso.inv ≫
          A.rightTotalLocallyUnitalFunctor.map f ≫ A.rightRegularTotalLocallyUnitalIso.hom))
          (Nat.add_zero n) := by
  change A.rightLocallyUnitalExtIso A.rightRegularTotalLocallyUnitalIso n
    (A.rightLocallyUnitalExtLinearEquiv M A.rightRegularCoproduct n
      (x.comp (Abelian.Ext.mk₀ f) (Nat.add_zero n))) = _
  rw [A.rightLocallyUnitalExtLinearEquiv_postcomp]
  exact A.rightLocallyUnitalExtIso_conjugation A.rightRegularTotalLocallyUnitalIso n _ _

namespace ASResolution
variable {A} {Q : CutQuiver} {w : Q.LiftVertex} (S : A.ASResolution Q w)

noncomputable def extTotalAlgebraLinearEquiv (n : ℕ) :
    Abelian.Ext.{v} (A.rightTotalLocallyUnitalModule (A.simpleRightModule (Q.height w)))
      A.totalAlgebraRightLocallyUnitalModule n ≃ₗ[k]
        A.leftModuleTotalSpace (A.rightModuleExtLeft (A.simpleRightModule (Q.height w)) n) :=
  (A.rightRegularExtGrLinearEquiv (A.simpleRightModule (Q.height w)) n).symm.trans
    (S.extRegularCoproductLinearEquiv n)

theorem extTotalAlgebraLinearEquiv_action (n : ℕ) {i j : ℤ} (a : A.Hom i j)
    (x : Abelian.Ext.{v} (A.rightTotalLocallyUnitalModule (A.simpleRightModule (Q.height w)))
      A.totalAlgebraRightLocallyUnitalModule n) :
    S.extTotalAlgebraLinearEquiv n
      (x.comp (Abelian.Ext.mk₀ (A.totalAlgebraLeftComponentMap a)) (Nat.add_zero n)) =
        A.leftModuleTotalAction (A.rightModuleExtLeft (A.simpleRightModule (Q.height w)) n) a
          (S.extTotalAlgebraLinearEquiv n x) := by
  obtain ⟨x,rfl⟩ :=
    (A.rightRegularExtGrLinearEquiv (A.simpleRightModule (Q.height w)) n).surjective x
  dsimp only [totalAlgebraLeftComponentMap]
  rw [← A.rightRegularExtGrLinearEquiv_postcomp (A.simpleRightModule (Q.height w)) n
    (A.rightRegularCoproductAction a)]
  change S.extRegularCoproductLinearEquiv n
    ((A.rightRegularExtGrLinearEquiv (A.simpleRightModule (Q.height w)) n).symm
      ((A.rightRegularExtGrLinearEquiv (A.simpleRightModule (Q.height w)) n)
        (x.comp (Abelian.Ext.mk₀ (A.rightRegularCoproductAction a)) (Nat.add_zero n)))) = _
  rw [LinearEquiv.symm_apply_apply]
  simp only [extTotalAlgebraLinearEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  change S.extRegularCoproductLinearEquiv n
    (x.comp (Abelian.Ext.mk₀ (A.rightRegularCoproductAction a)) (Nat.add_zero n)) =
      A.leftModuleTotalAction (A.rightModuleExtLeft (A.simpleRightModule (Q.height w)) n) a
        (S.extRegularCoproductLinearEquiv n x)
  exact congrArg (fun f => f.hom x) (S.extRegularCoproductEquiv_action n a)

theorem extTotalAlgebraLinearEquiv_representation (n : ℕ) (a : A.totalAlgebra)
    (x : Abelian.Ext.{v} (A.rightTotalLocallyUnitalModule (A.simpleRightModule (Q.height w)))
      A.totalAlgebraRightLocallyUnitalModule n) :
    S.extTotalAlgebraLinearEquiv n
      (x.comp (Abelian.Ext.mk₀ (A.totalAlgebraLeftMap a)) (Nat.add_zero n)) =
        A.leftTotalRepresentation (A.rightModuleExtLeft (A.simpleRightModule (Q.height w)) n) a
          (S.extTotalAlgebraLinearEquiv n x) := by
  obtain ⟨a,rfl⟩ := A.totalAlgebraEquiv.surjective a
  induction a using DFinsupp.induction with
  | h0 =>
    rw [A.totalAlgebraEquiv.map_zero, A.totalAlgebraLeftMap_zero, Abelian.Ext.mk₀_zero,
      Abelian.Ext.comp_zero, LinearEquiv.map_zero,
      (A.leftTotalRepresentation (A.rightModuleExtLeft (A.simpleRightModule (Q.height w)) n)).map_zero,
      LinearMap.zero_apply]
  | ha p b a _ _ ih =>
    rw [A.totalAlgebraEquiv.map_add, A.totalAlgebraLeftMap_add, Abelian.Ext.mk₀_add,
      Abelian.Ext.comp_add, LinearEquiv.map_add,
      (A.leftTotalRepresentation (A.rightModuleExtLeft (A.simpleRightModule (Q.height w)) n)).map_add,
      LinearMap.add_apply, ih]
    congr 1
    rcases p with ⟨i,j⟩
    change S.extTotalAlgebraLinearEquiv n
      (x.comp (Abelian.Ext.mk₀ (A.totalAlgebraLeftMap (A.totalAlgebraComponent b))) (Nat.add_zero n)) =
        A.leftTotalRepresentation (A.rightModuleExtLeft (A.simpleRightModule (Q.height w)) n)
          (A.totalAlgebraComponent b) (S.extTotalAlgebraLinearEquiv n x)
    rw [A.totalAlgebraLeftMap_component, A.leftTotalRepresentation_component]
    exact S.extTotalAlgebraLinearEquiv_action n b x

end ASResolution
end ASGinzburg.ZAlgebra
