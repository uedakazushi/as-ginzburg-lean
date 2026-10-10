import ASGinzburg.GradedOrdinaryModuleData
import ASGinzburg.OrdinaryIdealActionDirectSum
import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-! Actual bounded graded projective covers on ordinary modules. This
packages a constructed epimorphism and its genuine radical kernel; it
does not assert existence of covers for an arbitrary ring. -/
namespace ASGinzburg
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]
variable {A : ℤ → Submodule k R}

structure GradedOrdinaryProjectiveCover (M : GradedOrdinaryModuleData k R A)
    (b : ℤ) (J : Ideal R) where
  source : GradedOrdinaryModuleData k R A
  boundedBelow : source.BoundedBelow b
  π : source.ringModule ⟶ M.ringModule
  preservesGrade : source.PreservesGrade M π
  projective : Projective source.ringModule
  epi : Epi π
  kernel_minimal : ∀ x : source.ringModule, π x = 0 →
    x ∈ ordinaryIdealActionSpan k R source.ringModule J

namespace GradedOrdinaryProjectiveCover
variable (M : GradedOrdinaryModuleData k R A) (b : ℤ) (J : Ideal R)

noncomputable def ofExists
    (h : ∃ (P : ModuleCat.{v} R) (G : ℤ → Submodule k P) (π : P ⟶ M.ringModule),
      Projective P ∧ DirectSum.IsInternal G ∧
        (∀ q, q < b → G q = ⊥) ∧
        (∀ p q : ℤ, ∀ r ∈ A p, ∀ x ∈ G q, r • x ∈ G (p + q)) ∧
        (∀ q x, x ∈ G q → π x ∈ M.grade q) ∧ Epi π ∧
        (∀ x : P, π x = 0 → x ∈ ordinaryIdealActionSpan k R P J)) :
    GradedOrdinaryProjectiveCover M b J := by
  classical
  let P := h.choose
  let G := h.choose_spec.choose
  let π := h.choose_spec.choose_spec.choose
  have hp := h.choose_spec.choose_spec.choose_spec
  exact {
    source := ⟨P, G, hp.2.1, hp.2.2.2.1⟩
    boundedBelow := hp.2.2.1
    π := π
    preservesGrade := hp.2.2.2.2.1
    projective := hp.1
    epi := hp.2.2.2.2.2.1
    kernel_minimal := hp.2.2.2.2.2.2
  }

end GradedOrdinaryProjectiveCover

abbrev GradedOrdinaryBoundedModule (k : Type u) [Field k]
    (R : Type v) [Ring R] [Algebra k R] (A : ℤ → Submodule k R) (b : ℤ) :=
  {M : GradedOrdinaryModuleData k R A // M.BoundedBelow b}

end ASGinzburg
