import work.ASGinzburgDraft.GradedOrdinaryProjectiveCover
import Mathlib.RingTheory.Finiteness.Basic

/-! Finite ordinary projective covers retain all genuine graded cover
data and the actual finite-generation proof for their source. -/
namespace ASGinzburg
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]
variable {A : ℤ → Submodule k R}

structure FiniteGradedOrdinaryProjectiveCover (M : GradedOrdinaryModuleData k R A)
    (b : ℤ) (J : Ideal R) extends GradedOrdinaryProjectiveCover M b J where
  finite : Module.Finite R source.ringModule

namespace FiniteGradedOrdinaryProjectiveCover
variable (M : GradedOrdinaryModuleData k R A) (b : ℤ) (J : Ideal R)

noncomputable def ofExists
    (h : ∃ (P : ModuleCat.{v} R) (G : ℤ → Submodule k P) (π : P ⟶ M.ringModule),
      Module.Finite R P ∧ Projective P ∧ DirectSum.IsInternal G ∧
        (∀ q, q < b → G q = ⊥) ∧
        (∀ p q : ℤ, ∀ r ∈ A p, ∀ x ∈ G q, r • x ∈ G (p + q)) ∧
        (∀ q x, x ∈ G q → π x ∈ M.grade q) ∧ Epi π ∧
        (∀ x : P, π x = 0 → x ∈ ordinaryIdealActionSpan k R P J)) :
    FiniteGradedOrdinaryProjectiveCover M b J := by
  classical
  let P := h.choose
  let G := h.choose_spec.choose
  let π := h.choose_spec.choose_spec.choose
  have hp := h.choose_spec.choose_spec.choose_spec
  exact {
    toGradedOrdinaryProjectiveCover := {
      source := ⟨P,G,hp.2.2.1,hp.2.2.2.2.1⟩
      boundedBelow := hp.2.2.2.1
      π := π
      preservesGrade := hp.2.2.2.2.2.1
      projective := hp.2.1
      epi := hp.2.2.2.2.2.2.1
      kernel_minimal := hp.2.2.2.2.2.2.2
    }
    finite := hp.1
  }

instance source_finite (C : FiniteGradedOrdinaryProjectiveCover M b J) :
    Module.Finite R C.source.ringModule := C.finite

end FiniteGradedOrdinaryProjectiveCover
end ASGinzburg
