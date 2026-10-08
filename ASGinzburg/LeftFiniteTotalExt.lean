import ASGinzburg.LeftRegularExtComparison
import ASGinzburg.LeftFiniteRegularExtComparison
import ASGinzburg.RegularRightMultiplication

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)
  (hAS : A.ASRegular Q) (M : A.LeftModule) (hM : A.leftFiniteDimensionalProperty M)

noncomputable def leftFiniteDimensionalExtTotalAlgebraLinearEquiv (n : ℕ) :
    Abelian.Ext.{v} (A.leftTotalLocallyUnitalModule M)
      A.totalAlgebraLeftLocallyUnitalModule n ≃ₗ[k]
        A.rightModuleTotalSpace (A.leftModuleExtRight M n) :=
  (A.leftRegularExtGrLinearEquiv M n).symm.trans
    (A.leftFiniteDimensionalExtRegularCoproductLinearEquiv Q hAS M hM n)

theorem leftFiniteDimensionalExtTotalAlgebraLinearEquiv_action (n : ℕ) {i j : ℤ} (a : A.Hom i j)
    (x : Abelian.Ext.{v} (A.leftTotalLocallyUnitalModule M)
      A.totalAlgebraLeftLocallyUnitalModule n) :
    A.leftFiniteDimensionalExtTotalAlgebraLinearEquiv Q hAS M hM n
      (x.comp (Abelian.Ext.mk₀ (A.totalAlgebraRightComponentMap a)) (Nat.add_zero n)) =
        A.rightModuleTotalAction (A.leftModuleExtRight M n) a
          (A.leftFiniteDimensionalExtTotalAlgebraLinearEquiv Q hAS M hM n x) := by
  obtain ⟨x,rfl⟩ :=
    (A.leftRegularExtGrLinearEquiv M n).surjective x
  dsimp only [totalAlgebraRightComponentMap]
  rw [← A.leftRegularExtGrLinearEquiv_postcomp M n
    (A.leftRegularCoproductAction a)]
  change A.leftFiniteDimensionalExtRegularCoproductLinearEquiv Q hAS M hM n
    ((A.leftRegularExtGrLinearEquiv M n).symm
      ((A.leftRegularExtGrLinearEquiv M n)
        (x.comp (Abelian.Ext.mk₀ (A.leftRegularCoproductAction a)) (Nat.add_zero n)))) = _
  rw [LinearEquiv.symm_apply_apply]
  simp only [leftFiniteDimensionalExtTotalAlgebraLinearEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  change A.leftFiniteDimensionalExtRegularCoproductLinearEquiv Q hAS M hM n
    (x.comp (Abelian.Ext.mk₀ (A.leftRegularCoproductAction a)) (Nat.add_zero n)) =
      A.rightModuleTotalAction (A.leftModuleExtRight M n) a
        (A.leftFiniteDimensionalExtRegularCoproductLinearEquiv Q hAS M hM n x)
  exact congrArg (fun f => f.hom x) (A.leftFiniteDimensionalExtRegularCoproductEquiv_action Q hAS M hM n a)

set_option maxRecDepth 4096 in
theorem leftFiniteDimensionalExtTotalAlgebraLinearEquiv_representation (n : ℕ) (a : A.totalAlgebra)
    (x : Abelian.Ext.{v} (A.leftTotalLocallyUnitalModule M)
      A.totalAlgebraLeftLocallyUnitalModule n) :
    A.leftFiniteDimensionalExtTotalAlgebraLinearEquiv Q hAS M hM n
      (x.comp (Abelian.Ext.mk₀ (A.totalAlgebraRightMap a)) (Nat.add_zero n)) =
        (A.rightTotalRepresentation (A.leftModuleExtRight M n) a).unop
          (A.leftFiniteDimensionalExtTotalAlgebraLinearEquiv Q hAS M hM n x) := by
  obtain ⟨a,rfl⟩ := A.totalAlgebraEquiv.surjective a
  induction a using DFinsupp.induction with
  | h0 =>
    rw [A.totalAlgebraEquiv.map_zero,A.totalAlgebraRightMap_zero,Abelian.Ext.mk₀_zero,
      Abelian.Ext.comp_zero,LinearEquiv.map_zero,
      (A.rightTotalRepresentation (A.leftModuleExtRight M n)).map_zero,
      MulOpposite.unop_zero,LinearMap.zero_apply]
  | ha p b a _ _ ih =>
    rw [A.totalAlgebraEquiv.map_add,A.totalAlgebraRightMap_add,Abelian.Ext.mk₀_add,
      Abelian.Ext.comp_add,LinearEquiv.map_add,
      (A.rightTotalRepresentation (A.leftModuleExtRight M n)).map_add,
      MulOpposite.unop_add,LinearMap.add_apply,ih]
    congr 1
    rcases p with ⟨i,j⟩
    change A.leftFiniteDimensionalExtTotalAlgebraLinearEquiv Q hAS M hM n
      (x.comp (Abelian.Ext.mk₀ (A.totalAlgebraRightMap (A.totalAlgebraComponent b))) (Nat.add_zero n)) =
        (A.rightTotalRepresentation (A.leftModuleExtRight M n) (A.totalAlgebraComponent b)).unop
          (A.leftFiniteDimensionalExtTotalAlgebraLinearEquiv Q hAS M hM n x)
    rw [A.totalAlgebraRightMap_component,A.rightTotalRepresentation_component]
    exact A.leftFiniteDimensionalExtTotalAlgebraLinearEquiv_action Q hAS M hM n b x

end ASGinzburg.ZAlgebra
