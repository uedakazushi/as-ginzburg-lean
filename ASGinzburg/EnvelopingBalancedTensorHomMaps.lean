import ASGinzburg.EnvelopingBalancedTensorHom
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Right-module surjections remain surjective under the actual
enveloping-valued Hom functor, using the vector-space basis of M. -/
namespace ASGinzburg
open scoped TensorProduct
universe u v w z z'
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module Rᵐᵒᵖ M]
variable [IsScalarTower k Rᵐᵒᵖ M]
variable {X : Type z} [AddCommGroup X] [Module k X] [Module Rᵐᵒᵖ X]
variable [IsScalarTower k Rᵐᵒᵖ X]
variable {Y : Type z'} [AddCommGroup Y] [Module k Y] [Module Rᵐᵒᵖ Y]
variable [IsScalarTower k Rᵐᵒᵖ Y]

noncomputable def envelopingBalancedTensorHomMap (f : X →ₗ[Rᵐᵒᵖ] Y) :
    letI := envelopingBalancedTensorHomModule k R M X
    letI := envelopingBalancedTensorHomModule k R M Y
    BalancedTensorHom k R M X →ₗ[AlgebraEnvelopingRing k R] BalancedTensorHom k R M Y := by
  letI := envelopingBalancedTensorHomModule k R M X
  letI := envelopingBalancedTensorHomModule k R M Y
  let fk := f.restrictScalars k
  exact {
    toFun := fun g => fk.comp (balancedTensorHomLinearEquiv k R M X g)
    map_add' := fun g h => by
      apply balancedTensorHom_ext k R M Y
      intro x
      exact f.map_add (g x) (h x)
    map_smul' := fun t g => by
      apply balancedTensorHom_ext k R M Y
      intro x
      let h : BalancedTensorHom k R M Y :=
        fk.comp (balancedTensorHomLinearEquiv k R M X g)
      refine TensorProduct.inductionOn (motive := fun t =>
        f ((t • g) x) = (t • h) x) t ?_ ?_
      · intro a b
        change f (((a ⊗ₜ[k] b) • g) x)=
          ((a ⊗ₜ[k] b) • h) x
        rw [envelopingBalancedTensorHomModule_tmul_apply,
          envelopingBalancedTensorHomModule_tmul_apply]
        exact f.map_smul b (g (MulOpposite.op a • x))
      · intro a b ha hb
        simp only [add_smul,balancedTensorHom_add_apply,f.map_add,ha,hb]}

theorem envelopingBalancedTensorHomMap_apply (f : X →ₗ[Rᵐᵒᵖ] Y)
    (g : BalancedTensorHom k R M X) (x : M) :
    envelopingBalancedTensorHomMap k R M f g x=f (g x) := rfl

theorem envelopingBalancedTensorHomMap_surjective (f : X →ₗ[Rᵐᵒᵖ] Y)
    (hf : Function.Surjective f) :
    Function.Surjective (envelopingBalancedTensorHomMap k R M f) := by
  intro g
  obtain ⟨h,hh⟩ := Module.projective_lifting_property (f.restrictScalars k)
    (balancedTensorHomLinearEquiv k R M Y g) hf
  refine ⟨(balancedTensorHomLinearEquiv k R M X).symm h,?_⟩
  apply balancedTensorHom_ext k R M Y
  intro x
  exact congrArg (fun e : M →ₗ[k] Y => e x) hh

end ASGinzburg
