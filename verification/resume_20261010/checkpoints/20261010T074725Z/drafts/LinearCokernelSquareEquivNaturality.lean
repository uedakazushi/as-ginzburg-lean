import work.ASGinzburgDraft.LinearCokernelSquareEquiv

/-! Naturality of the genuine cokernel equivalence under maps preserving
the actual boundary subspaces. -/
namespace ASGinzburg
universe u v₁ v₂ v₁' v₂' w₁ w₂ w₁' w₂'
variable {k : Type u} [Field k]
variable {M₁ : Type v₁} [AddCommGroup M₁] [Module k M₁]
variable {M₂ : Type v₂} [AddCommGroup M₂] [Module k M₂]
variable {M₁' : Type v₁'} [AddCommGroup M₁'] [Module k M₁']
variable {M₂' : Type v₂'} [AddCommGroup M₂'] [Module k M₂']
variable {N₁ : Type w₁} [AddCommGroup N₁] [Module k N₁]
variable {N₂ : Type w₂} [AddCommGroup N₂] [Module k N₂]
variable {N₁' : Type w₁'} [AddCommGroup N₁'] [Module k N₁']
variable {N₂' : Type w₂'} [AddCommGroup N₂'] [Module k N₂']

theorem linearCokernelSquareEquiv_naturality_apply
    (f₁ : M₁ →ₗ[k] N₁) (f₂ : M₂ →ₗ[k] N₂)
    (g₁ : M₁' →ₗ[k] N₁') (g₂ : M₂' →ₗ[k] N₂')
    (eM₁ : M₁ ≃ₗ[k] M₁') (eM₂ : M₂ ≃ₗ[k] M₂')
    (eN₁ : N₁ ≃ₗ[k] N₁') (eN₂ : N₂ ≃ₗ[k] N₂')
    (h₁ : ∀ x, eN₁ (f₁ x) = g₁ (eM₁ x))
    (h₂ : ∀ x, eN₂ (f₂ x) = g₂ (eM₂ x))
    (a : N₁ →ₗ[k] N₂) (b : N₁' →ₗ[k] N₂')
    (ha : LinearMap.range f₁ ≤ (LinearMap.range f₂).comap a)
    (hb : LinearMap.range g₁ ≤ (LinearMap.range g₂).comap b)
    (h : ∀ x, eN₂ (a x) = b (eN₁ x)) (z : N₁ ⧸ LinearMap.range f₁) :
    linearCokernelSquareEquiv f₂ g₂ eM₂ eN₂ h₂
        ((LinearMap.range f₁).mapQ (LinearMap.range f₂) a ha z) =
      (LinearMap.range g₁).mapQ (LinearMap.range g₂) b hb
        (linearCokernelSquareEquiv f₁ g₁ eM₁ eN₁ h₁ z) := by
  obtain ⟨x, rfl⟩ := (LinearMap.range f₁).mkQ_surjective z
  change (LinearMap.range g₂).mkQ (eN₂ (a x)) =
    (LinearMap.range g₂).mkQ (b (eN₁ x))
  rw [h]

theorem linearCokernelSquareEquiv_naturality
    (f₁ : M₁ →ₗ[k] N₁) (f₂ : M₂ →ₗ[k] N₂)
    (g₁ : M₁' →ₗ[k] N₁') (g₂ : M₂' →ₗ[k] N₂')
    (eM₁ : M₁ ≃ₗ[k] M₁') (eM₂ : M₂ ≃ₗ[k] M₂')
    (eN₁ : N₁ ≃ₗ[k] N₁') (eN₂ : N₂ ≃ₗ[k] N₂')
    (h₁ : ∀ x, eN₁ (f₁ x) = g₁ (eM₁ x))
    (h₂ : ∀ x, eN₂ (f₂ x) = g₂ (eM₂ x))
    (a : N₁ →ₗ[k] N₂) (b : N₁' →ₗ[k] N₂')
    (ha : LinearMap.range f₁ ≤ (LinearMap.range f₂).comap a)
    (hb : LinearMap.range g₁ ≤ (LinearMap.range g₂).comap b)
    (h : ∀ x, eN₂ (a x) = b (eN₁ x)) :
    (linearCokernelSquareEquiv f₂ g₂ eM₂ eN₂ h₂).toLinearMap.comp
        ((LinearMap.range f₁).mapQ (LinearMap.range f₂) a ha) =
      ((LinearMap.range g₁).mapQ (LinearMap.range g₂) b hb).comp
        (linearCokernelSquareEquiv f₁ g₁ eM₁ eN₁ h₁).toLinearMap := by
  apply LinearMap.ext
  intro z
  exact linearCokernelSquareEquiv_naturality_apply
    f₁ f₂ g₁ g₂ eM₁ eM₂ eN₁ eN₂ h₁ h₂ a b ha hb h z

end ASGinzburg
