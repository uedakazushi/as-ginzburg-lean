import ASGinzburg.ASResolutionExtColimits
import ASGinzburg.ASDualityLeftComponents
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Ext into the concrete coproduct of all P_i, before the missing Gr(A) equivalence. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum
universe u v
variable {k : Type u} [Field k]

/-- Projection to the one surviving summand is an equivalence, with its actual inclusion inverse. -/
noncomputable def directSumSingleSupportLinearEquiv {I : Type} [DecidableEq I]
    (M : I → Type v) [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)]
    (i₀ : I) (h : ∀ i, i ≠ i₀ → ∀ x : M i, x = 0) :
    (⨁ i, M i) ≃ₗ[k] M i₀ where
  toFun x := x i₀
  invFun x := DirectSum.lof k I M i₀ x
  left_inv x := by
    apply DFinsupp.ext
    intro i
    by_cases hi : i = i₀
    · subst i; exact DirectSum.lof_apply k i₀ (x i₀)
    · change (DFinsupp.single i₀ (x i₀)) i = x i
      rw [DFinsupp.single_eq_of_ne hi, h i hi (x i)]
  right_inv x := DirectSum.lof_apply k i₀ x
  map_add' x y := rfl
  map_smul' r x := rfl

namespace ZAlgebra
variable (A : ZAlgebra.{u,v} k)

/-- The explicit right-module coproduct, retained as such until Gr(A) comparison is proved. -/
noncomputable def rightRegularCoproduct : A.RightModule := ∐ fun i : ℤ => A.representable i

/-- Component j is the genuine direct sum of e_i A e_j. -/
noncomputable def rightRegularCoproductComponentIso (j : ℤ) :
    (A.rightModuleEvaluation j).obj A.rightRegularCoproduct ≅
      ModuleCat.of k (⨁ i : ℤ, A.Hom j i) :=
  PreservesCoproduct.iso (A.rightModuleEvaluation j) (fun i : ℤ => A.representable i) ≪≫
    ModuleCat.coprodIsoDirectSum _

abbrev leftModuleTotalSpace (M : A.LeftModule) : Type v :=
  ⨁ i : ℤ, (A.leftModuleEvaluation i).obj M

noncomputable def leftModuleTotalIso {M N : A.LeftModule} (e : M ≅ N) :
    A.leftModuleTotalSpace M ≃ₗ[k] A.leftModuleTotalSpace N :=
  DFinsupp.mapRange.linearEquiv (fun i => (A.leftModuleEvaluation i).mapIso e |>.toLinearEquiv)

namespace ASResolution
variable {A} {Q : CutQuiver} {x : Q.LiftVertex} (R : A.ASResolution Q x)

/-- Actual Ext into the coproduct is the finite-support total space of the proved Ext left module. -/
noncomputable def extRegularCoproductLinearEquiv (n : ℕ) :
    Abelian.Ext.{v} (A.simpleRightModule (Q.height x)) A.rightRegularCoproduct n ≃ₗ[k]
      A.leftModuleTotalSpace (A.rightModuleExtLeft (A.simpleRightModule (Q.height x)) n) :=
  R.simpleExtDirectSumLinearEquiv n (fun i : ℤ => A.representable i)

end ASResolution

theorem leftModuleTotalSpace_eq_zero_of_isZero {M : A.LeftModule} (hM : IsZero M)
    (x : A.leftModuleTotalSpace M) : x = 0 := by
  apply DFinsupp.ext
  intro i
  have hi := Functor.map_isZero (A.leftModuleEvaluation i) hM
  letI := ModuleCat.subsingleton_of_isZero hi
  exact Subsingleton.elim _ _

noncomputable def simpleLeftModuleTotalEquiv (i : ℤ) :
    A.leftModuleTotalSpace (A.simpleLeftModule i) ≃ₗ[k]
      (A.leftModuleEvaluation i).obj (A.simpleLeftModule i) :=
  directSumSingleSupportLinearEquiv _ i (fun j hj x => by
    have hz := A.simpleLeftModule_off_diagonal i j hj
    letI := ModuleCat.subsingleton_of_isZero hz
    exact Subsingleton.elim _ _)

variable (Q : CutQuiver)

theorem ASRegular.extRegularCoproduct_off_three_eq_zero (h : A.ASRegular Q)
    (x : Q.LiftVertex) (n : ℕ) (hn : n ≠ 3)
    (e : Abelian.Ext.{v} (A.simpleRightModule (Q.height x)) A.rightRegularCoproduct n) : e = 0 := by
  apply ((h.resolution A Q x).extRegularCoproductLinearEquiv n).injective
  rw [LinearEquiv.map_zero]
  exact A.leftModuleTotalSpace_eq_zero_of_isZero (h.extLeft_off_degree_three A Q x n hn) _

/-- The right-coproduct Ext has the same underlying vector space as the left simple.
This does not claim an unimplemented Gr(A) equivalence or a total algebra left action. -/
noncomputable def ASRegular.extRegularCoproductThreeEquiv (h : A.ASRegular Q) (x : Q.LiftVertex) :
    Abelian.Ext.{v} (A.simpleRightModule (Q.height x)) A.rightRegularCoproduct 3 ≃ₗ[k]
      (A.leftModuleEvaluation (Q.height (Q.tau.symm x))).obj
        (A.simpleLeftModule (Q.height (Q.tau.symm x))) :=
  ((h.resolution A Q x).extRegularCoproductLinearEquiv 3).trans
    ((A.leftModuleTotalIso (h.extLeftThreeIsoSimple A Q x)).trans
      (A.simpleLeftModuleTotalEquiv (Q.height (Q.tau.symm x))))

theorem ASRegular.extRegularCoproductThree_finrank (h : A.ASRegular Q) (x : Q.LiftVertex) :
    Module.finrank k
      (Abelian.Ext.{v} (A.simpleRightModule (Q.height x)) A.rightRegularCoproduct 3) = 1 :=
  (h.extRegularCoproductThreeEquiv A Q x).finrank_eq.trans
    (A.simpleLeftModule_diagonal_finrank _)

noncomputable def ASRegular.extRegularCoproductThreeScalarEquiv (h : A.ASRegular Q)
    (x : Q.LiftVertex) :
    Abelian.Ext.{v} (A.simpleRightModule (Q.height x)) A.rightRegularCoproduct 3 ≃ₗ[k] k :=
  (h.extRegularCoproductThreeEquiv A Q x).trans
    ((A.simpleLeftModuleDiagonalIso (Q.height (Q.tau.symm x))).toLinearEquiv.trans
      (A.scalarEndEquiv (Q.height (Q.tau.symm x))).symm)

theorem ASRegular.extRegularCoproductFinite (h : A.ASRegular Q) (x : Q.LiftVertex) (n : ℕ) :
    Module.Finite k
      (Abelian.Ext.{v} (A.simpleRightModule (Q.height x)) A.rightRegularCoproduct n) := by
  by_cases hn : n = 3
  · subst n
    exact Module.Finite.of_injective (h.extRegularCoproductThreeScalarEquiv A Q x).toLinearMap
      (h.extRegularCoproductThreeScalarEquiv A Q x).injective
  · letI : Subsingleton (Abelian.Ext.{v} (A.simpleRightModule (Q.height x))
        A.rightRegularCoproduct n) := ⟨fun a b => by
      rw [h.extRegularCoproduct_off_three_eq_zero A Q x n hn a,
        h.extRegularCoproduct_off_three_eq_zero A Q x n hn b]⟩
    infer_instance

theorem ASRegular.extRegularCoproduct_finrank (h : A.ASRegular Q) (x : Q.LiftVertex) (n : ℕ) :
    Module.finrank k
      (Abelian.Ext.{v} (A.simpleRightModule (Q.height x)) A.rightRegularCoproduct n) =
        if n = 3 then 1 else 0 := by
  by_cases hn : n = 3
  · subst n; simpa using h.extRegularCoproductThree_finrank A Q x
  · letI : Subsingleton (Abelian.Ext.{v} (A.simpleRightModule (Q.height x))
        A.rightRegularCoproduct n) := ⟨fun a b => by
      rw [h.extRegularCoproduct_off_three_eq_zero A Q x n hn a,
        h.extRegularCoproduct_off_three_eq_zero A Q x n hn b]⟩
    simp only [if_neg hn, Module.finrank_zero_of_subsingleton]

end ZAlgebra
end ASGinzburg
