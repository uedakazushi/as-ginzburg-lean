import ASGinzburg.RightModuleRadical
import ASGinzburg.RepresentableHomColimits
import Mathlib.Algebra.Category.ModuleCat.Products

/-! Finite coproduct radicals and their actual quotient components. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)
variable {I : Type} [Fintype I] [DecidableEq I] (g : I → A.RightModule)

noncomputable def rightFiniteCoproductProjection (a : I) : ∐ g ⟶ g a :=
  Sigma.desc (fun b => if h : b=a then eqToHom (congrArg g h) else 0)

@[simp] theorem rightFiniteCoproduct_inclusion_projection (a : I) :
    Sigma.ι g a ≫ A.rightFiniteCoproductProjection g a = 𝟙 _ := by
  simp [rightFiniteCoproductProjection]

theorem rightFiniteCoproduct_inclusion_projection_off (a b : I) (h : b≠a) :
    Sigma.ι g b ≫ A.rightFiniteCoproductProjection g a = 0 := by
  simp [rightFiniteCoproductProjection,h]

noncomputable def rightFiniteCoproductComponentIso (i : ℤ) :
    (A.rightModuleEvaluation i).obj (∐ g) ≅
      ModuleCat.of k (⨁ a, (A.rightModuleEvaluation i).obj (g a)) :=
  PreservesCoproduct.iso (A.rightModuleEvaluation i) g ≪≫ ModuleCat.coprodIsoDirectSum _

theorem rightFiniteCoproductComponentIso_lof_inv (i : ℤ) (a : I)
    (x : (A.rightModuleEvaluation i).obj (g a)) :
    (A.rightFiniteCoproductComponentIso g i).inv.hom (DirectSum.lof k I _ a x) =
      ((A.rightModuleEvaluation i).map (Sigma.ι g a)).hom x := by
  have H : ModuleCat.ofHom (DirectSum.lof k I
      (fun a => (A.rightModuleEvaluation i).obj (g a)) a) ≫
      (A.rightFiniteCoproductComponentIso g i).inv =
      (A.rightModuleEvaluation i).map (Sigma.ι g a) := by
    dsimp only [rightFiniteCoproductComponentIso,Iso.trans_inv]
    rw [← Category.assoc]
    erw [ModuleCat.lof_coprodIsoDirectSum_inv]
    rw [PreservesCoproduct.inv_hom,ι_comp_sigmaComparison]
  exact congrArg (fun f => f.hom x) H

noncomputable def rightFiniteCoproductPiEquiv (i : ℤ) :
    (A.rightModuleEvaluation i).obj (∐ g) ≃ₗ[k]
      (∀ a, (A.rightModuleEvaluation i).obj (g a)) :=
  (A.rightFiniteCoproductComponentIso g i).toLinearEquiv.trans DFinsupp.linearEquivFunOnFintype

theorem rightFiniteCoproductPiEquiv_projection (i : ℤ) (a : I)
    (x : (A.rightModuleEvaluation i).obj (∐ g)) :
    A.rightFiniteCoproductPiEquiv g i x a =
      ((A.rightModuleEvaluation i).map (A.rightFiniteCoproductProjection g a)).hom x := by
  obtain ⟨x,rfl⟩ := (A.rightFiniteCoproductComponentIso g i).toLinearEquiv.symm.surjective x
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add,hx,hy]
  | of b x =>
    change A.rightFiniteCoproductPiEquiv g i
      ((A.rightFiniteCoproductComponentIso g i).inv.hom (DirectSum.lof k I _ b x)) a = _
    have hleft : A.rightFiniteCoproductPiEquiv g i
        ((A.rightFiniteCoproductComponentIso g i).inv.hom (DirectSum.lof k I _ b x)) a =
        DFinsupp.single (β := fun a => (A.rightModuleEvaluation i).obj (g a)) b x a := by
      change ((A.rightFiniteCoproductComponentIso g i).toLinearEquiv
        ((A.rightFiniteCoproductComponentIso g i).toLinearEquiv.symm
          (DirectSum.lof k I _ b x))) a = _
      rw [LinearEquiv.apply_symm_apply]
      rfl
    rw [hleft]
    change DFinsupp.single (β := fun a => (A.rightModuleEvaluation i).obj (g a)) b x a =
      ((A.rightModuleEvaluation i).map (A.rightFiniteCoproductProjection g a)).hom
        ((A.rightFiniteCoproductComponentIso g i).inv.hom (DirectSum.lof k I _ b x))
    rw [A.rightFiniteCoproductComponentIso_lof_inv]
    have H := congrArg (fun f => f.hom x)
      ((A.rightModuleEvaluation i).map_comp (Sigma.ι g b) (A.rightFiniteCoproductProjection g a))
    by_cases h : b=a
    · subst b
      simpa using H
    · have Hz := congrArg (fun f => ((A.rightModuleEvaluation i).map f).hom x)
        (A.rightFiniteCoproduct_inclusion_projection_off g a b h)
      simp only [Functor.map_zero] at Hz
      have Hzero := H.symm.trans Hz
      simpa only [DFinsupp.single_eq_of_ne (Ne.symm h)] using Hzero.symm

theorem rightFiniteCoproductPiEquiv_single_symm (i : ℤ) (a : I)
    (x : (A.rightModuleEvaluation i).obj (g a)) :
    (A.rightFiniteCoproductPiEquiv g i).symm (Pi.single a x) =
      ((A.rightModuleEvaluation i).map (Sigma.ι g a)).hom x := by
  change (A.rightFiniteCoproductComponentIso g i).inv.hom
    (DFinsupp.equivFunOnFintype.symm (Pi.single a x)) = _
  rw [show DFinsupp.equivFunOnFintype.symm (Pi.single a x) =
    DirectSum.lof k I (fun a => (A.rightModuleEvaluation i).obj (g a)) a x by
      apply DFinsupp.ext; intro b; rfl]
  exact A.rightFiniteCoproductComponentIso_lof_inv g i a x

theorem rightFiniteCoproduct_radical_iff (i : ℤ)
    (x : (A.rightModuleEvaluation i).obj (∐ g)) :
    x ∈ A.positiveActionSpan (∐ g) i ↔
      ∀ a, A.rightFiniteCoproductPiEquiv g i x a ∈ A.positiveActionSpan (g a) i := by
  constructor
  · intro hx a
    rw [A.rightFiniteCoproductPiEquiv_projection]
    exact A.positiveActionSpan_map_mem (A.rightFiniteCoproductProjection g a) i hx
  · intro hx
    have H := congrArg (A.rightFiniteCoproductPiEquiv g i).symm
      (Finset.univ_sum_single (A.rightFiniteCoproductPiEquiv g i x))
    rw [map_sum,LinearEquiv.symm_apply_apply] at H
    rw [← H]
    apply (A.positiveActionSpan (∐ g) i).sum_mem
    intro a ha
    rw [A.rightFiniteCoproductPiEquiv_single_symm]
    exact A.positiveActionSpan_map_mem (Sigma.ι g a) i (hx a)

end ASGinzburg.ZAlgebra
