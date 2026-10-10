import ASGinzburg.ScalarProductSeparability

/-! Give the ordinary scalar-product enveloping algebra coordinates
indexed by the ordered pair of tensor factors. The genuine tensor of
two vertex delta functions becomes the delta function at that pair. -/
namespace ASGinzburg
open scoped TensorProduct
universe u v
variable (k : Type u) [Field k] (I : Type v) [Fintype I] [DecidableEq I]

noncomputable def scalarProductPairFunctionEquiv :
    (I → I → k) ≃ₐ[k] (I × I → k) where
  toFun f a := f a.2 a.1
  invFun f i j := f (j,i)
  left_inv _ := rfl
  right_inv f := by funext a; rcases a with ⟨i,j⟩; rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

noncomputable def scalarProductPairEnvelopingEquiv :
    ((I → k) ⊗[k] (I → k)ᵐᵒᵖ) ≃ₐ[k] (I × I → k) :=
  (scalarProductEnvelopingEquiv k I).trans (scalarProductPairFunctionEquiv k I)

theorem scalarProductPairEnvelopingEquiv_tmul_apply (f g : I → k) (a : I × I) :
    scalarProductPairEnvelopingEquiv k I (f ⊗ₜ[k] MulOpposite.op g) a =
      f a.1 * g a.2 := by
  change (Algebra.TensorProduct.piScalarRight k k (I → k) I)
    (f ⊗ₜ[k] g) a.2 a.1 = _
  rw [Algebra.TensorProduct.piScalarRight_tmul_apply]
  change g a.2 * f a.1 = _
  exact mul_comm _ _

theorem scalarProductPairEnvelopingEquiv_delta (i j : I) :
    scalarProductPairEnvelopingEquiv k I
      (Pi.single i (1:k) ⊗ₜ[k] MulOpposite.op (Pi.single j (1:k))) =
        Pi.single (i,j) (1:k) := by
  funext a
  rcases a with ⟨i',j'⟩
  rw [scalarProductPairEnvelopingEquiv_tmul_apply]
  by_cases hi : i' = i <;> by_cases hj : j' = j
  · subst i'; subst j'; simp
  · simp [hj]
  · simp [hi]
  · simp [hi]

end ASGinzburg
