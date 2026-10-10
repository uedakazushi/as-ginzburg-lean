import work.ASGinzburgDraft.AlgebraEnvelopingTensorRegularFree
import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-! Tensors of ordinary free right and left modules are actual free
right enveloping modules, with the product of their basis indices. -/
namespace ASGinzburg
open scoped TensorProduct
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (I : Type w) (J : Type z)

attribute [local instance] tensorRightEnvelopingModule
attribute [local instance 2000] Semiring.toModule

noncomputable def tensorRightEnvelopingFinsuppDistribution :
    ((I →₀ R) ⊗[k] (J →₀ R)) ≃ₗ[(AlgebraEnvelopingRing k R)ᵐᵒᵖ]
      ((I × J) →₀ (R ⊗[k] R)) where
  toFun := finsuppTensorFinsupp k k R R I J
  invFun := (finsuppTensorFinsupp k k R R I J).symm
  left_inv := (finsuppTensorFinsupp k k R R I J).left_inv
  right_inv := (finsuppTensorFinsupp k k R R I J).right_inv
  map_add' := map_add (finsuppTensorFinsupp k k R R I J)
  map_smul' e x := by
    change finsuppTensorFinsupp k k R R I J (e • x) =
      e • finsuppTensorFinsupp k k R R I J x
    obtain ⟨e, rfl⟩ := MulOpposite.op_surjective e
    induction e using TensorProduct.induction_on with
    | zero =>
        simp only [MulOpposite.op_zero, zero_smul, map_zero]
        apply Finsupp.ext
        intro p
        simp only [Finsupp.zero_apply, Finsupp.smul_apply, zero_smul]
    | tmul a b =>
        induction x using TensorProduct.induction_on with
        | zero => simp only [smul_zero, map_zero]
        | tmul f g =>
            change finsuppTensorFinsupp k k R R I J
              (MulOpposite.op (a ⊗ₜ[k] MulOpposite.op b.unop) • (f ⊗ₜ[k] g)) =
                MulOpposite.op (a ⊗ₜ[k] MulOpposite.op b.unop) •
                  finsuppTensorFinsupp k k R R I J (f ⊗ₜ[k] g)
            rw [tensorRightEnvelopingModule_tmul_smul]
            apply Finsupp.ext
            rintro ⟨i, j⟩
            simp only [finsuppTensorFinsupp_apply, Finsupp.smul_apply,
              tensorRightEnvelopingModule_tmul_smul]
        | add x y hx hy =>
            simp only [smul_add, map_add, hx, hy]
            apply Finsupp.ext
            intro p
            simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_add]
    | add e f he hf => simp only [MulOpposite.op_add, add_smul, map_add, he, hf]

theorem tensorRightEnvelopingFinsuppDistribution_apply_tmul (f : I →₀ R) (g : J →₀ R)
    (i : I) (j : J) :
    tensorRightEnvelopingFinsuppDistribution k R I J (f ⊗ₜ[k] g) (i, j) =
      f i ⊗ₜ[k] g j :=
  finsuppTensorFinsupp_apply k k R R I J f g i j

noncomputable def tensorRightEnvelopingFinsuppEquiv :
    ((I →₀ R) ⊗[k] (J →₀ R)) ≃ₗ[(AlgebraEnvelopingRing k R)ᵐᵒᵖ]
      ((I × J) →₀ (AlgebraEnvelopingRing k R)ᵐᵒᵖ) :=
  (tensorRightEnvelopingFinsuppDistribution k R I J).trans
    (Finsupp.mapRange.linearEquiv (tensorRightEnvelopingRegularEquiv k R))

theorem tensorRightEnvelopingFinsuppEquiv_single_tmul_single
    (i : I) (j : J) (a b : R) :
    tensorRightEnvelopingFinsuppEquiv k R I J
      ((Finsupp.single i a) ⊗ₜ[k] (Finsupp.single j b)) =
        Finsupp.single (i, j) (MulOpposite.op (a ⊗ₜ[k] MulOpposite.op b)) := by
  classical
  change Finsupp.mapRange (tensorRightEnvelopingRegularEquiv k R)
    (map_zero (tensorRightEnvelopingRegularEquiv k R))
    (finsuppTensorFinsupp k k R R I J
      ((Finsupp.single i a) ⊗ₜ[k] (Finsupp.single j b))) = _
  rw [finsuppTensorFinsupp_single, Finsupp.mapRange_single]
  rfl

theorem tensorRightEnvelopingFinsupp_free :
    Module.Free (AlgebraEnvelopingRing k R)ᵐᵒᵖ ((I →₀ R) ⊗[k] (J →₀ R)) :=
  Module.Free.of_equiv (tensorRightEnvelopingFinsuppEquiv k R I J).symm

theorem tensorRightEnvelopingFinsupp_projective :
    Module.Projective (AlgebraEnvelopingRing k R)ᵐᵒᵖ ((I →₀ R) ⊗[k] (J →₀ R)) := by
  letI := tensorRightEnvelopingFinsupp_free k R I J
  exact Module.Projective.of_free

end ASGinzburg
