import ASGinzburg.AlgebraEnvelopingRegularModule
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! A surjective algebra map induces a surjective map of the genuine
unsigned enveloping algebras. Its actual two-sided kernel is the sum of
the two extended factor kernels. -/
namespace ASGinzburg
open scoped TensorProduct
universe u v w
variable (k : Type u) [Field k]
variable {R : Type v} [Ring R] [Algebra k R]
variable {S : Type w} [Ring S] [Algebra k S]
variable (f : R →ₐ[k] S)

noncomputable def algebraEnvelopingMap :
    AlgebraEnvelopingRing k R →ₐ[k] AlgebraEnvelopingRing k S :=
  Algebra.TensorProduct.map f f.op

theorem algebraEnvelopingMap_tmul (a b : R) :
    algebraEnvelopingMap k f (a ⊗ₜ[k] MulOpposite.op b) =
      f a ⊗ₜ[k] MulOpposite.op (f b) := rfl

theorem algebraHom_op_surjective (hf : Function.Surjective f) :
    Function.Surjective f.op := by
  intro x
  obtain ⟨a, ha⟩ := hf x.unop
  exact ⟨MulOpposite.op a, congrArg MulOpposite.op ha⟩

theorem algebraEnvelopingMap_surjective (hf : Function.Surjective f) :
    Function.Surjective (algebraEnvelopingMap k f) :=
  TensorProduct.map_surjective hf (algebraHom_op_surjective k f hf)

noncomputable def algebraEnvelopingMapKernel : Ideal (AlgebraEnvelopingRing k R) :=
  RingHom.ker (algebraEnvelopingMap k f)

noncomputable instance algebraEnvelopingMapKernelTwoSided :
    (algebraEnvelopingMapKernel k f).IsTwoSided := by
  unfold algebraEnvelopingMapKernel
  infer_instance

theorem mem_algebraEnvelopingMapKernel (x : AlgebraEnvelopingRing k R) :
    x ∈ algebraEnvelopingMapKernel k f ↔ algebraEnvelopingMap k f x = 0 := Iff.rfl

theorem algebraEnvelopingMapKernel_eq_sup (hf : Function.Surjective f) :
    algebraEnvelopingMapKernel k f =
      (RingHom.ker f).map
        (Algebra.TensorProduct.includeLeft : R →ₐ[k] AlgebraEnvelopingRing k R) ⊔
      (RingHom.ker f.op).map
        (Algebra.TensorProduct.includeRight : Rᵐᵒᵖ →ₐ[k] AlgebraEnvelopingRing k R) :=
  Algebra.TensorProduct.map_ker f f.op hf (algebraHom_op_surjective k f hf)

noncomputable def algebraEnvelopingMapQuotientAlgEquiv (hf : Function.Surjective f) :
    (AlgebraEnvelopingRing k R ⧸ algebraEnvelopingMapKernel k f) ≃ₐ[k]
      AlgebraEnvelopingRing k S :=
  Ideal.quotientKerAlgEquivOfSurjective (algebraEnvelopingMap_surjective k f hf)

end ASGinzburg
