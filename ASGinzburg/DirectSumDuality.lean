import ASGinzburg.SmallVectorDuality

/-! The canonical map from the direct sum of component duals to the dual of
the total direct sum is bijective when the original components have finite support. -/
namespace ASGinzburg
open scoped DirectSum
universe u v w
variable {k : Type u} [Field k] {I : Type w} [DecidableEq I] (V : I → Type v)
  [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
variable (U : Type v) [AddCommGroup U] [Module k U]

noncomputable def directSumDualInto : (⨁ i, V i →ₗ[k] U) →ₗ[k] ((⨁ i, V i) →ₗ[k] U) :=
  DirectSum.toModule k I _ (fun i => {
    toFun := fun f => f.comp (DirectSum.component k I V i)
    map_add' := by intros; ext; rfl
    map_smul' := by intros; ext; rfl })

theorem directSumDualInto_lof (i : I) (f : V i →ₗ[k] U) :
    directSumDualInto (k := k) V U (DirectSum.lof k I (fun i => V i →ₗ[k] U) i f) =
      f.comp (DirectSum.component k I V i) := DirectSum.toModule_lof _ _ _

theorem directSumDualInto_eval_lof (f : ⨁ i, V i →ₗ[k] U) (i : I) (x : V i) :
    directSumDualInto (k := k) V U f (DirectSum.lof k I V i x) = f i x := by
  classical
  induction f using DirectSum.induction_on with
  | zero => simp
  | of j g =>
    rw [show DirectSum.of (fun i => V i →ₗ[k] U) j g =
      DirectSum.lof k I (fun i => V i →ₗ[k] U) j g from rfl,directSumDualInto_lof]
    by_cases h : j=i
    · subst j
      simp
    · change g (DFinsupp.single (β := V) i x j) = (DFinsupp.single (β := fun t => V t →ₗ[k] U) j g i) x
      rw [DFinsupp.single_eq_of_ne h,DFinsupp.single_eq_of_ne (Ne.symm h)]
      simp
  | add f g hf hg => simp [hf,hg]

theorem directSumDualInto_injective : Function.Injective (directSumDualInto (k := k) V U) := by
  intro f g h
  apply DFinsupp.ext
  intro i
  apply LinearMap.ext
  intro x
  simpa only [directSumDualInto_eval_lof] using congrArg (fun t => t (DirectSum.lof k I V i x)) h

theorem directSumDualInto_surjective (S : Finset I)
    (hS : ∀ i, i ∉ S → ∀ x : V i, x=0) : Function.Surjective (directSumDualInto (k := k) V U) := by
  classical
  intro f
  refine ⟨∑ i ∈ S, DirectSum.lof k I (fun i => V i →ₗ[k] U) i (f.comp (DirectSum.lof k I V i)),?_⟩
  apply DirectSum.linearMap_ext
  intro i
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply,LinearMap.comp_apply,directSumDualInto_eval_lof]
  by_cases hi : i ∈ S
  · have hEq : (∑ j ∈ S, DirectSum.lof k I (fun i => V i →ₗ[k] U) j
        (f.comp (DirectSum.lof k I V j))) i = f.comp (DirectSum.lof k I V i) := by
      change (∑ j ∈ S, DFinsupp.single j (f.comp (DirectSum.lof k I V j))) i = _
      rw [DFinsupp.finset_sum_apply]
      simp [DFinsupp.single_apply,hi]
    rw [hEq]
    rfl
  · have hx : x=0 := hS i hi x
    subst x
    simp

noncomputable def directSumDualIntoEquiv (S : Finset I)
    (hS : ∀ i, i ∉ S → ∀ x : V i, x=0) :
    (⨁ i, V i →ₗ[k] U) ≃ₗ[k] ((⨁ i, V i) →ₗ[k] U) :=
  LinearEquiv.ofBijective (directSumDualInto (k := k) V U)
    ⟨directSumDualInto_injective (k := k) V U,directSumDualInto_surjective (k := k) V U S hS⟩
end ASGinzburg

namespace ASGinzburg
open CategoryTheory
open scoped DirectSum
universe u v w
variable {k : Type u} [Field k] {I : Type w} [DecidableEq I]
    (V : I → ModuleCat.{v} k) (U : ModuleCat.{v} k)

noncomputable def moduleCatDirectSumDualIntoLinearMap :
    (⨁ i, V i ⟶ U) →ₗ[k] ((⨁ i, V i) →ₗ[k] U) :=
  (directSumDualInto (k := k) (fun i => V i) U).comp
    (DFinsupp.mapRange.linearEquiv (fun i => ModuleCat.homLinearEquiv (S := k) (M := V i) (N := U))).toLinearMap

theorem moduleCatDirectSumDualIntoLinearMap_eval_lof (f : ⨁ i, V i ⟶ U) (i : I) (x : V i) :
    moduleCatDirectSumDualIntoLinearMap V U f (DirectSum.lof k I (fun i => V i) i x) = (f i).hom x := by
  change directSumDualInto (k := k) (fun i => V i) U _ (DirectSum.lof k I (fun i => V i) i x) = _
  rw [directSumDualInto_eval_lof]
  rfl

theorem moduleCatDirectSumDualIntoLinearMap_bijective (S : Finset I)
    (hS : ∀ i, i ∉ S → ∀ x : V i, x=0) :
    Function.Bijective (moduleCatDirectSumDualIntoLinearMap V U) := by
  let e : (⨁ i, V i ⟶ U) ≃ₗ[k] (⨁ i, (V i) →ₗ[k] U) :=
    DFinsupp.mapRange.linearEquiv (fun i => ModuleCat.homLinearEquiv (S := k) (M := V i) (N := U))
  exact (show Function.Bijective (directSumDualInto (k := k) (fun i => V i) U) from
    ⟨directSumDualInto_injective (k := k) _ _,directSumDualInto_surjective (k := k) _ _ S hS⟩).comp e.bijective
end ASGinzburg
