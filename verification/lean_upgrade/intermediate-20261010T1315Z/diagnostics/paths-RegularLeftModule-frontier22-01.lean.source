import ASGinzburg.LeftRegularTotalAlgebra
import ASGinzburg.RegularRightModule
import Mathlib.Algebra.Module.TransferInstance

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)
noncomputable def totalAlgebraLeftUnitizationModule : Module A.totalUnitization A.totalAlgebra := by
  letI := A.leftTotalUnitizationModule A.leftRegularCoproduct
  exact A.leftRegularTotalAlgebraEquiv.symm.toAddEquiv.module A.totalUnitization

noncomputable def totalAlgebraLeftModule : ModuleCat.{v} A.totalUnitization := by
  letI : Module A.totalUnitization A.totalAlgebra := A.totalAlgebraLeftUnitizationModule
  exact ModuleCat.of A.totalUnitization A.totalAlgebra

theorem totalAlgebraLeftModule_smul (r : A.totalUnitization) (x : A.totalAlgebra) :
    letI : Module A.totalUnitization A.totalAlgebra := A.totalAlgebraLeftUnitizationModule
    letI : SMul A.totalUnitization A.totalAlgebra :=
      A.totalAlgebraLeftUnitizationModule.toDistribMulAction.toMulAction.toSMul
    (r • x : A.totalAlgebra) = r.fst • x + r.snd * x := by
  letI : Module A.totalUnitization A.totalAlgebra := A.totalAlgebraLeftUnitizationModule
  letI : SMul A.totalUnitization A.totalAlgebra :=
    A.totalAlgebraLeftUnitizationModule.toDistribMulAction.toMulAction.toSMul
  change A.leftRegularTotalAlgebraEquiv
    (r.fst • A.leftRegularTotalAlgebraEquiv.symm x +
      (A.leftTotalRepresentation A.leftRegularCoproduct r.snd)
        (A.leftRegularTotalAlgebraEquiv.symm x)) = _
  rw [map_add, map_smul, A.leftRegularTotalAlgebraEquiv_representation,
    LinearEquiv.apply_symm_apply]

noncomputable def leftRegularTotalModuleIso :
    A.leftTotalModule A.leftRegularCoproduct ≅ A.totalAlgebraLeftModule := by
  letI := A.leftTotalUnitizationModule A.leftRegularCoproduct
  letI : Module A.totalUnitization A.totalAlgebra := A.totalAlgebraLeftUnitizationModule
  let e : A.leftModuleTotalSpace A.leftRegularCoproduct ≃ₗ[A.totalUnitization]
      A.totalAlgebra :=
    { A.leftRegularTotalAlgebraEquiv.toAddEquiv with
      map_smul' := by
        intro r x
        change A.leftRegularTotalAlgebraEquiv (r • x) =
          A.leftRegularTotalAlgebraEquiv
            (r • A.leftRegularTotalAlgebraEquiv.symm (A.leftRegularTotalAlgebraEquiv x))
        rw [LinearEquiv.symm_apply_apply] }
  exact e.toModuleIso

theorem totalAlgebraLeftModule_locally_unital :
    A.leftLocallyUnitalProperty A.totalAlgebraLeftModule := by
  letI := A.leftTotalUnitizationModule A.leftRegularCoproduct
  intro x
  obtain ⟨s,hs⟩ := A.leftTotalModule_locally_unital A.leftRegularCoproduct
    (A.leftRegularTotalAlgebraEquiv.symm x)
  refine ⟨s,?_⟩
  change A.leftRegularTotalAlgebraEquiv
    ((A.totalAlgebraLocalUnit s : A.totalUnitization) •
      A.leftRegularTotalAlgebraEquiv.symm x) = x
  rw [hs, LinearEquiv.apply_symm_apply]

noncomputable def totalAlgebraLeftLocallyUnitalModule : A.LeftLocallyUnitalModule :=
  ⟨A.totalAlgebraLeftModule, A.totalAlgebraLeftModule_locally_unital⟩

noncomputable def leftRegularTotalLocallyUnitalIso :
    A.leftTotalLocallyUnitalModule A.leftRegularCoproduct ≅
      A.totalAlgebraLeftLocallyUnitalModule :=
  A.leftLocallyUnitalProperty.isoMk A.leftRegularTotalModuleIso

theorem leftRegularMatrixElement_totalMap {i j q : ℤ} (a : A.Hom i j) (b : A.Hom j q) :
    A.leftTotalLinearMap (A.leftRegularCoproductAction a) (A.leftRegularMatrixElement b) =
      A.leftRegularMatrixElement (A.comp b a) := by
  change A.leftTotalLinearMap (A.leftRegularCoproductAction a)
    (DirectSum.lof k ℤ _ q
      (((Sigma.ι (fun t : ℤ => A.leftRepresentable t) j).hom.app (⟨q⟩ : A.Obj)).hom b)) = _
  rw [A.leftTotalLinearMap_lof]
  apply congrArg (DirectSum.lof k ℤ (fun t => (A.leftModuleEvaluation t).obj A.leftRegularCoproduct) q)
  exact congrArg (fun f => (f.hom.app (⟨q⟩ : A.Obj)).hom b)
    (A.leftRegularCoproduct_inclusion_action a)

theorem leftRegularMatrixElement_totalMap_off {i j p q : ℤ} (a : A.Hom i j)
    (b : A.Hom p q) (hpj : p ≠ j) :
    A.leftTotalLinearMap (A.leftRegularCoproductAction a) (A.leftRegularMatrixElement b) = 0 := by
  change A.leftTotalLinearMap (A.leftRegularCoproductAction a)
    (DirectSum.lof k ℤ _ q
      (((Sigma.ι (fun t : ℤ => A.leftRepresentable t) p).hom.app (⟨q⟩ : A.Obj)).hom b)) = _
  rw [A.leftTotalLinearMap_lof]
  have h := congrArg (fun f => (f.hom.app (⟨q⟩ : A.Obj)).hom b)
    (A.leftRegularCoproduct_inclusion_action_off a p hpj)
  change _ = (0 : A.leftModuleTotalSpace A.leftRegularCoproduct)
  have hz : ((A.leftRegularCoproductAction a).hom.app (⟨q⟩ : A.Obj)).hom
      (((Sigma.ι (fun t : ℤ => A.leftRepresentable t) p).hom.app (⟨q⟩ : A.Obj)).hom b) = 0 := h
  rw [hz,map_zero]

theorem leftRegularTotalAlgebraEquiv_totalMap {i j : ℤ} (a : A.Hom i j)
    (x : A.leftModuleTotalSpace A.leftRegularCoproduct) :
    A.leftRegularTotalAlgebraEquiv (A.leftTotalLinearMap (A.leftRegularCoproductAction a) x) =
      A.leftRegularTotalAlgebraEquiv x * A.totalAlgebraComponent a := by
  obtain ⟨x,rfl⟩ := A.leftRegularTotalComponentsEquiv.symm.surjective x
  induction x using DFinsupp.induction with
  | h0 => simp
  | ha p b x _ _ ih =>
    rw [map_add,map_add,map_add,map_add,add_mul,ih]
    congr 1
    rcases p with ⟨l,m⟩
    rw [A.leftRegularTotalComponentsEquiv_symm_single]
    by_cases hl : l=j
    · subst l
      rw [A.leftRegularMatrixElement_totalMap,A.leftRegularTotalAlgebraEquiv_matrixElement,
        A.leftRegularTotalAlgebraEquiv_matrixElement,A.totalAlgebraComponent_mul]
    · rw [A.leftRegularMatrixElement_totalMap_off a b hl,map_zero,
        A.leftRegularTotalAlgebraEquiv_matrixElement,A.totalAlgebraComponent_mul_off a b (Ne.symm hl)]

noncomputable def totalAlgebraRightComponentMap {i j : ℤ} (a : A.Hom i j) :
    A.totalAlgebraLeftLocallyUnitalModule ⟶ A.totalAlgebraLeftLocallyUnitalModule :=
  A.leftRegularTotalLocallyUnitalIso.inv ≫
    A.leftTotalLocallyUnitalFunctor.map (A.leftRegularCoproductAction a) ≫
      A.leftRegularTotalLocallyUnitalIso.hom

theorem totalAlgebraRightComponentMap_apply {i j : ℤ} (a : A.Hom i j) (x : A.totalAlgebra) :
    (A.totalAlgebraRightComponentMap a).hom.hom x = x * A.totalAlgebraComponent a := by
  change A.leftRegularTotalAlgebraEquiv
    (A.leftTotalLinearMap (A.leftRegularCoproductAction a)
      (A.leftRegularTotalAlgebraEquiv.symm x)) = _
  rw [A.leftRegularTotalAlgebraEquiv_totalMap,LinearEquiv.apply_symm_apply]

end ASGinzburg.ZAlgebra
