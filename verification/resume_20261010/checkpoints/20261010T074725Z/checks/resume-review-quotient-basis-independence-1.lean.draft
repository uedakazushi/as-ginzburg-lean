import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

/-! Any representatives whose actual quotient classes form a basis
are linearly independent in the original vector space. -/
namespace ASGinzburg
universe u v w
variable {k : Type u} [Field k] {M : Type v} [AddCommGroup M] [Module k M]
  {ι : Type w}

theorem quotientBasisRepresentatives_linearIndependent (p : Submodule k M)
    (b : Module.Basis ι k (M ⧸ p)) (f : ι → M) (hf : ∀ a, p.mkQ (f a) = b a) :
    LinearIndependent k f := by
  have h : p.mkQ ∘ f = b := funext hf
  have hli : LinearIndependent k (p.mkQ ∘ f) := h.symm ▸ b.linearIndependent
  exact LinearIndependent.of_comp p.mkQ hli

end ASGinzburg
