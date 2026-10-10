import Mathlib.LinearAlgebra.Quotient.Basic

/-! An actual stable linear operator descends to the actual submodule
quotient and commutes with its quotient map. -/
namespace ASGinzburg
universe u v
variable (k : Type u) [Field k] (M : Type v) [AddCommGroup M] [Module k M]
variable (S : Submodule k M) (f : M →ₗ[k] M)
variable (hf : ∀ x : M, x ∈ S → f x ∈ S)

noncomputable def stableSubmoduleQuotientOperator : (M ⧸ S) →ₗ[k] (M ⧸ S) :=
  S.liftQ (S.mkQ.comp f) (fun x hx => by
    change S.mkQ (f x)=0
    exact (Submodule.Quotient.mk_eq_zero S).mpr (hf x hx))

@[simp] theorem stableSubmoduleQuotientOperator_mkQ (x : M) :
    stableSubmoduleQuotientOperator k M S f hf (S.mkQ x) = S.mkQ (f x) := rfl

end ASGinzburg
