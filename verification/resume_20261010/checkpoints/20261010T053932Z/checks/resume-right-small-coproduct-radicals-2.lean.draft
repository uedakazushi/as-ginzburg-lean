import ASGinzburg.RightModuleRadical
import ASGinzburg.RepresentableHomColimits
import Mathlib.Algebra.Category.ModuleCat.Products

/-! Arbitrary small coproducts of actual right modules have the expected
componentwise positive radical. The reconstruction uses finite support,
so no finiteness condition is imposed on the family. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)
variable {I : Type v} [DecidableEq I] (g : I → A.RightModule)

noncomputable def rightSmallCoproductProjection (a : I) : ∐ g ⟶ g a :=
  Sigma.desc (fun b => if h : b=a then eqToHom (congrArg g h) else 0)

@[simp] theorem rightSmallCoproduct_inclusion_projection (a : I) :
    Sigma.ι g a ≫ A.rightSmallCoproductProjection g a = 𝟙 _ := by
  simp [rightSmallCoproductProjection]

theorem rightSmallCoproduct_inclusion_projection_off (a b : I) (h : b≠a) :
    Sigma.ι g b ≫ A.rightSmallCoproductProjection g a = 0 := by
  simp [rightSmallCoproductProjection,h]

noncomputable def rightSmallCoproductComponentIso (i : ℤ) :
    (A.rightModuleEvaluation i).obj (∐ g) ≅
      ModuleCat.of k (⨁ a, (A.rightModuleEvaluation i).obj (g a)) :=
  PreservesCoproduct.iso (A.rightModuleEvaluation i) g ≪≫ ModuleCat.coprodIsoDirectSum _

theorem rightSmallCoproductComponentIso_lof_inv (i : ℤ) (a : I)
    (x : (A.rightModuleEvaluation i).obj (g a)) :
    (A.rightSmallCoproductComponentIso g i).inv.hom (DirectSum.lof k I _ a x) =
      ((A.rightModuleEvaluation i).map (Sigma.ι g a)).hom x := by
  have H : ModuleCat.ofHom (DirectSum.lof k I
      (fun a => (A.rightModuleEvaluation i).obj (g a)) a) ≫
      (A.rightSmallCoproductComponentIso g i).inv =
      (A.rightModuleEvaluation i).map (Sigma.ι g a) := by
    dsimp only [rightSmallCoproductComponentIso,Iso.trans_inv]
    rw [← Category.assoc]
    erw [ModuleCat.lof_coprodIsoDirectSum_inv]
    rw [PreservesCoproduct.inv_hom,ι_comp_sigmaComparison]
  exact congrArg (fun f => f.hom x) H

theorem rightSmallCoproductComponentIso_projection (i : ℤ) (a : I)
    (x : (A.rightModuleEvaluation i).obj (∐ g)) :
    (A.rightSmallCoproductComponentIso g i).hom.hom x a =
      ((A.rightModuleEvaluation i).map (A.rightSmallCoproductProjection g a)).hom x := by
  obtain ⟨x,rfl⟩ := (A.rightSmallCoproductComponentIso g i).toLinearEquiv.symm.surjective x
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add,hx,hy]
  | of b x =>
    change (A.rightSmallCoproductComponentIso g i).hom.hom
      ((A.rightSmallCoproductComponentIso g i).inv.hom (DirectSum.lof k I _ b x)) a =
      ((A.rightModuleEvaluation i).map (A.rightSmallCoproductProjection g a)).hom
        ((A.rightSmallCoproductComponentIso g i).inv.hom (DirectSum.lof k I _ b x))
    have hleft : (A.rightSmallCoproductComponentIso g i).hom.hom
        ((A.rightSmallCoproductComponentIso g i).inv.hom (DirectSum.lof k I _ b x)) a =
        DFinsupp.single (β := fun a => (A.rightModuleEvaluation i).obj (g a)) b x a := by
      change ((A.rightSmallCoproductComponentIso g i).toLinearEquiv
        ((A.rightSmallCoproductComponentIso g i).toLinearEquiv.symm
          (DirectSum.lof k I _ b x))) a = _
      rw [LinearEquiv.apply_symm_apply]
      rfl
    rw [hleft]
    rw [A.rightSmallCoproductComponentIso_lof_inv]
    have H := congrArg (fun f => f.hom x)
      ((A.rightModuleEvaluation i).map_comp (Sigma.ι g b) (A.rightSmallCoproductProjection g a))
    by_cases h : b=a
    · subst b
      simpa using H
    · have Hz := congrArg (fun f => ((A.rightModuleEvaluation i).map f).hom x)
        (A.rightSmallCoproduct_inclusion_projection_off g a b h)
      simp only [Functor.map_zero] at Hz
      have Hzero := H.symm.trans Hz
      simpa only [DFinsupp.single_eq_of_ne (Ne.symm h)] using Hzero.symm

theorem rightSmallCoproduct_radical_iff (i : ℤ)
    (x : (A.rightModuleEvaluation i).obj (∐ g)) :
    x ∈ A.positiveActionSpan (∐ g) i ↔
      ∀ a, (A.rightSmallCoproductComponentIso g i).hom.hom x a ∈ A.positiveActionSpan (g a) i := by
  classical
  constructor
  · intro hx a
    rw [A.rightSmallCoproductComponentIso_projection]
    exact A.positiveActionSpan_map_mem (A.rightSmallCoproductProjection g a) i hx
  · intro hx
    let z := (A.rightSmallCoproductComponentIso g i).hom.hom x
    have H := congrArg (A.rightSmallCoproductComponentIso g i).inv.hom
      (DirectSum.sum_support_of z)
    rw [map_sum] at H
    have Hx : (A.rightSmallCoproductComponentIso g i).inv.hom z = x :=
      (A.rightSmallCoproductComponentIso g i).toLinearEquiv.symm_apply_apply x
    rw [Hx] at H
    rw [← H]
    apply (A.positiveActionSpan (∐ g) i).sum_mem
    intro a ha
    change (A.rightSmallCoproductComponentIso g i).inv.hom (DirectSum.lof k I _ a (z a)) ∈ _
    rw [A.rightSmallCoproductComponentIso_lof_inv]
    exact A.positiveActionSpan_map_mem (Sigma.ι g a) i (hx a)

end ASGinzburg.ZAlgebra
