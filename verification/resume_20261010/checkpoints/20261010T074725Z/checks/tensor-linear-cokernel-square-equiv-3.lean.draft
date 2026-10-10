import Mathlib.LinearAlgebra.Quotient.Basic

/-! A genuine commuting square of linear equivalences gives a genuine
linear equivalence of the cokernel quotient spaces, on their actual classes. -/
namespace ASGinzburg
universe u v v' w w'
variable {k : Type u} [Field k]
variable {M : Type v} [AddCommGroup M] [Module k M]
variable {M' : Type v'} [AddCommGroup M'] [Module k M']
variable {N : Type w} [AddCommGroup N] [Module k N]
variable {N' : Type w'} [AddCommGroup N'] [Module k N']
theorem linearMapRange_map_eq_of_equiv_square
    (f : M →ₗ[k] N) (g : M' →ₗ[k] N')
    (eM : M ≃ₗ[k] M') (eN : N ≃ₗ[k] N')
    (h : ∀ x, eN (f x) = g (eM x)) :
    (LinearMap.range f).map eN.toLinearMap = LinearMap.range g := by
  ext y
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨x, rfl⟩ := hz
    exact ⟨eM x, (h x).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨f (eM.symm x), ⟨eM.symm x, rfl⟩, ?_⟩
    change eN (f (eM.symm x)) = g x
    rw [h, eM.apply_symm_apply]

noncomputable def linearCokernelSquareEquiv
    (f : M →ₗ[k] N) (g : M' →ₗ[k] N')
    (eM : M ≃ₗ[k] M') (eN : N ≃ₗ[k] N')
    (h : ∀ x, eN (f x) = g (eM x)) :
    (N ⧸ LinearMap.range f) ≃ₗ[k] (N' ⧸ LinearMap.range g) :=
  Submodule.Quotient.equiv (LinearMap.range f) (LinearMap.range g) eN
    (linearMapRange_map_eq_of_equiv_square f g eM eN h)

@[simp] theorem linearCokernelSquareEquiv_mk
    (f : M →ₗ[k] N) (g : M' →ₗ[k] N')
    (eM : M ≃ₗ[k] M') (eN : N ≃ₗ[k] N')
    (h : ∀ x, eN (f x) = g (eM x)) (y : N) :
    linearCokernelSquareEquiv f g eM eN h ((LinearMap.range f).mkQ y) =
      (LinearMap.range g).mkQ (eN y) := rfl

end ASGinzburg
