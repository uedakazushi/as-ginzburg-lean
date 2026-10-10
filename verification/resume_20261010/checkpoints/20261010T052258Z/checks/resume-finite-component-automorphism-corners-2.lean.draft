import ASGinzburg.FiniteComponentIdempotents
import Mathlib.Algebra.Algebra.Equiv

/-! Vertex-fixed algebra automorphisms of the genuine finite convolution
algebra preserve every matrix corner. Their restrictions are actual linear
equivalences of the original morphism spaces. -/
namespace ASGinzburg.LinearComponentAlgebra
universe u v
variable {k : Type u} [Field k] {ι : Type v} [Fintype ι]
  (B : LinearComponentAlgebra k ι)

theorem totalIdempotent_mul_mul_eq_component (i j : ι) (x : B.Total) :
    B.totalIdempotent j * x * B.totalIdempotent i =
      B.totalComponent i j (x i j) := by
  classical
  funext p q
  by_cases hp : p = i
  · subst p
    by_cases hq : q = j
    · subst q
      change (∑ m, B.comp ((B.totalIdempotent j * x) m j)
        (B.totalIdempotent i i m)) = _
      rw [Finset.sum_eq_single i]
      · rw [show B.totalIdempotent i i i = B.id i by
          simp [totalIdempotent, totalComponent], B.id_comp]
        change (∑ l, B.comp (B.totalIdempotent j l j) (x i l)) =
          B.totalComponent i j (x i j) i j
        rw [Finset.sum_eq_single j]
        · simp [totalIdempotent, totalComponent, B.comp_id]
        · intro l _ hl
          simp [totalIdempotent, totalComponent, hl]
        · simp
      · intro m _ hm
        simp [totalIdempotent, totalComponent, Ne.symm hm]
      · simp
    · change (∑ m, B.comp ((B.totalIdempotent j * x) m q)
        (B.totalIdempotent i i m)) = _
      simp [totalComponent, hq]
      apply Finset.sum_eq_zero
      intro m _
      have hz : (B.totalIdempotent j * x) m q = 0 := by
        change (∑ l, B.comp (B.totalIdempotent j l q) (x m l)) = 0
        apply Finset.sum_eq_zero
        intro l _
        by_cases hl : l = j
        · subst l
          simp [totalIdempotent, totalComponent, hq]
        · simp [totalIdempotent, totalComponent, hl]
      rw [hz]
      simp
  · change (∑ m, B.comp ((B.totalIdempotent j * x) m q)
        (B.totalIdempotent i p m)) = _
    simp [totalIdempotent, totalComponent, hp]

theorem totalAlgEquiv_component_projection (E : B.Total ≃ₐ[k] B.Total)
    (hE : ∀ i, E (B.totalIdempotent i) = B.totalIdempotent i)
    (i j : ι) (x : B.Total) :
    E (B.totalComponent i j (x i j)) = B.totalComponent i j (E x i j) := by
  rw [← B.totalIdempotent_mul_mul_eq_component i j x,
    map_mul, map_mul, hE j, hE i, B.totalIdempotent_mul_mul_eq_component]

theorem totalAlgEquiv_symm_idempotent (E : B.Total ≃ₐ[k] B.Total)
    (hE : ∀ i, E (B.totalIdempotent i) = B.totalIdempotent i) (i : ι) :
    E.symm (B.totalIdempotent i) = B.totalIdempotent i := by
  apply E.injective
  rw [E.apply_symm_apply, hE i]

theorem totalAlgEquiv_component (E : B.Total ≃ₐ[k] B.Total)
    (hE : ∀ i, E (B.totalIdempotent i) = B.totalIdempotent i)
    (i j : ι) (a : B.Hom i j) :
    E (B.totalComponent i j a) =
      B.totalComponent i j (E (B.totalComponent i j a) i j) := by
  simpa only [B.totalComponent_apply_same] using
    B.totalAlgEquiv_component_projection E hE i j (B.totalComponent i j a)

noncomputable def totalAlgEquivComponentLinearEquiv (E : B.Total ≃ₐ[k] B.Total)
    (hE : ∀ i, E (B.totalIdempotent i) = B.totalIdempotent i) (i j : ι) :
    B.Hom i j ≃ₗ[k] B.Hom i j where
  toFun a := E (B.totalComponent i j a) i j
  invFun a := E.symm (B.totalComponent i j a) i j
  left_inv a := by
    change E.symm (B.totalComponent i j (E (B.totalComponent i j a) i j)) i j = a
    rw [← B.totalAlgEquiv_component E hE, E.symm_apply_apply,
      B.totalComponent_apply_same]
  right_inv a := by
    change E (B.totalComponent i j (E.symm (B.totalComponent i j a) i j)) i j = a
    rw [← B.totalAlgEquiv_component E.symm (B.totalAlgEquiv_symm_idempotent E hE),
      E.apply_symm_apply, B.totalComponent_apply_same]
  map_add' a b := by
    change ((E.toLinearEquiv.toLinearMap.comp (B.totalComponentLinear i j)) (a + b)) i j = _
    rw [map_add]
    rfl
  map_smul' c a := by
    change ((E.toLinearEquiv.toLinearMap.comp (B.totalComponentLinear i j)) (c • a)) i j = _
    rw [map_smul]
    rfl

@[simp] theorem totalAlgEquivComponentLinearEquiv_apply (E : B.Total ≃ₐ[k] B.Total)
    (hE : ∀ i, E (B.totalIdempotent i) = B.totalIdempotent i)
    (i j : ι) (a : B.Hom i j) :
    B.totalAlgEquivComponentLinearEquiv E hE i j a =
      E (B.totalComponent i j a) i j := rfl

theorem totalAlgEquivComponentLinearEquiv_component (E : B.Total ≃ₐ[k] B.Total)
    (hE : ∀ i, E (B.totalIdempotent i) = B.totalIdempotent i)
    (i j : ι) (a : B.Hom i j) :
    B.totalComponent i j (B.totalAlgEquivComponentLinearEquiv E hE i j a) =
      E (B.totalComponent i j a) :=
  (B.totalAlgEquiv_component E hE i j a).symm

end ASGinzburg.LinearComponentAlgebra
