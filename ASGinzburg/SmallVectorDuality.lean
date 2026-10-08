import ASGinzburg.FiniteProjectivePresentations
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace ASGinzburg
open CategoryTheory
universe u v
variable {k : Type u} [Field k] {U M : Type v}
  [AddCommGroup U] [Module k U] [AddCommGroup M] [Module k M]

def dualIntoEvaluation : M →ₗ[k] ((M →ₗ[k] U) →ₗ[k] U) where
  toFun x := {
    toFun := fun f => f x
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

noncomputable def dualIntoToDual (e : k ≃ₗ[k] U) : (M →ₗ[k] U) ≃ₗ[k] Module.Dual k M :=
  LinearEquiv.arrowCongr (LinearEquiv.refl k M) e.symm

theorem dualIntoEvaluation_bijective [Module.Finite k M] (e : k ≃ₗ[k] U) :
    Function.Bijective (dualIntoEvaluation (k := k) (M := M) (U := U)) := by
  let t : (M →ₗ[k] U) ≃ₗ[k] Module.Dual k M := dualIntoToDual (M := M) e
  let q : ((M →ₗ[k] U) →ₗ[k] U) ≃ₗ[k] Module.Dual k (Module.Dual k M) :=
    LinearEquiv.arrowCongr t e.symm
  have H (x : M) : q (dualIntoEvaluation (U := U) x) = Module.Dual.eval k M x := by
    ext f
    change e.symm ((t.symm f) x) = f x
    simp [t,dualIntoToDual,LinearEquiv.arrowCongr]
  constructor
  · intro x y h
    apply (Module.bijective_dual_eval k M).injective
    rw [← H x,← H y,h]
  · intro g
    refine ⟨(Module.evalEquiv k M).symm (q g),?_⟩
    apply q.injective
    rw [H]
    exact (Module.evalEquiv k M).apply_symm_apply (q g)

theorem dualInto_finite [Module.Finite k M] (e : k ≃ₗ[k] U) :
    Module.Finite k (M →ₗ[k] U) :=
  Module.Finite.equiv (dualIntoToDual (M := M) e).symm

/-- The target U remains in the original small universe. -/
def moduleCatDualIntoFunctor (U : ModuleCat.{v} k) : (ModuleCat.{v} k)ᵒᵖ ⥤ ModuleCat.{v} k :=
  (linearYoneda k (ModuleCat.{v} k)).obj U
end ASGinzburg


namespace ASGinzburg
open scoped DirectSum
universe u v w
variable {k : Type u} [Field k] {I : Type w} (V : I → Type v)
  [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
theorem directSum_finite_of_finite_support (S : Finset I)
    (hS : ∀ i, i ∉ S → ∀ x : V i, x=0)
    (hV : ∀ i : S, Module.Finite k (V i)) : Module.Finite k (⨁ i, V i) := by
  letI : ∀ i : S, Module.Finite k (V i) := hV
  apply FiniteDimensional.of_injective (LinearMap.pi (fun i : S => DirectSum.component k I V i))
  intro x y hxy
  apply DFinsupp.ext
  intro i
  by_cases hi : i ∈ S
  · exact congrArg (fun a => a ⟨i,hi⟩) hxy
  · rw [hS i hi (x i),hS i hi (y i)]
end ASGinzburg


namespace ASGinzburg
open CategoryTheory
universe u v
variable {k : Type u} [Field k] (U M : ModuleCat.{v} k)

def moduleCatDualIntoEvaluation : M ⟶
    ((moduleCatDualIntoFunctor U).rightOp ⋙ moduleCatDualIntoFunctor U).obj M :=
  ModuleCat.ofHom {
    toFun x := ModuleCat.ofHom {
      toFun t := t.hom x
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
    map_add' := by intros; ext; simp
    map_smul' := by intros; ext; simp }

theorem moduleCatDualIntoEvaluation_bijective [Module.Finite k M] (e : k ≃ₗ[k] U) :
    Function.Bijective (moduleCatDualIntoEvaluation U M).hom := by
  let t : (M ⟶ U) ≃ₗ[k] (M →ₗ[k] U) := ModuleCat.homLinearEquiv (S := k)
  let q : ((ModuleCat.of k (M ⟶ U)) ⟶ U) ≃ₗ[k] ((M →ₗ[k] U) →ₗ[k] U) :=
    (ModuleCat.homLinearEquiv (S := k)).trans
      (LinearEquiv.arrowCongr t (LinearEquiv.refl k U))
  have H (x : M) : q ((moduleCatDualIntoEvaluation U M).hom x) =
      dualIntoEvaluation (U := U) x := by
    ext f
    rfl
  have B := dualIntoEvaluation_bijective (M := M) e
  constructor
  · intro x y h
    apply B.injective
    rw [← H x,← H y,h]
  · intro g
    obtain ⟨x,hx⟩ := B.surjective (q g)
    refine ⟨x,q.injective ?_⟩
    rw [H,hx]
end ASGinzburg

