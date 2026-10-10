import ASGinzburg.EnvelopingBalancedTensorHom
import ASGinzburg.EnvelopingBalancedTensorRightMaps

/-! Tensor-Hom correspondence retaining the actual right R action and
the actual enveloping-module action. -/
namespace ASGinzburg
open scoped TensorProduct
universe u v w z z'
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module Rᵐᵒᵖ M]
variable [IsScalarTower k Rᵐᵒᵖ M]
variable (P : Type z) [AddCommGroup P] [Module k P]
variable [Module (AlgebraEnvelopingRing k R) P] [IsScalarTower k (AlgebraEnvelopingRing k R) P]
variable (X : Type z') [AddCommGroup X] [Module k X] [Module Rᵐᵒᵖ X]
variable [IsScalarTower k Rᵐᵒᵖ X]

noncomputable def envelopingBalancedTensorCurry :
    letI := envelopingBalancedTensorRightModule k R M P
    letI := envelopingBalancedTensorHomModule k R M X
    (EnvelopingBalancedTensorSpace k R M P →ₗ[Rᵐᵒᵖ] X) →
      (P →ₗ[AlgebraEnvelopingRing k R] BalancedTensorHom k R M X) := by
  letI := envelopingLeftModule k R P
  letI := envelopingLeftScalarTower k R P
  letI := envelopingRightModule k R P
  letI := envelopingBalancedTensorRightModule k R M P
  letI := envelopingBalancedTensorRightScalarTower k R M P
  letI := envelopingBalancedTensorHomModule k R M X
  intro f
  let g := balancedTensorCurry k R M P X (f.restrictScalars k)
  exact {
    toFun := g
    map_add' := g.map_add
    map_smul' := fun t p => by
      apply balancedTensorHom_ext k R M X
      intro x
      refine TensorProduct.induction_on t ?_ ?_ ?_
      · have h : g ((0 : AlgebraEnvelopingRing k R) • p)=
            (0 : AlgebraEnvelopingRing k R) • g p := by
          have hp : (0 : AlgebraEnvelopingRing k R) • p=0 :=
            (inferInstance : Module (AlgebraEnvelopingRing k R) P).zero_smul p
          have hg : (0 : AlgebraEnvelopingRing k R) • g p=0 :=
            (envelopingBalancedTensorHomModule k R M X).zero_smul (g p)
          exact (congrArg g hp).trans (g.map_zero.trans hg.symm)
        exact congrArg (fun h : BalancedTensorHom k R M X => h x) h
      · intro a b
        change f (balancedTensorTmul k R M P x ((a ⊗ₜ[k] b) • p))=
          ((a ⊗ₜ[k] b) • g p) x
        rw [envelopingModule_tmul_smul,← balancedTensorTmul_balance,
          envelopingBalancedTensorHomModule_tmul_apply]
        change f (balancedTensorTmul k R M P (MulOpposite.op a • x) (b • p))=
          b • f (balancedTensorTmul k R M P (MulOpposite.op a • x) p)
        rw [← envelopingBalancedTensorRightModule_tmul,f.map_smul]
      · intro a b ha hb
        simp only [add_smul,map_add,balancedTensorHom_add_apply,ha,hb]}

theorem envelopingBalancedTensorCurry_apply :
    letI := envelopingLeftModule k R P
    letI := envelopingBalancedTensorRightModule k R M P
    letI := envelopingBalancedTensorHomModule k R M X
    ∀ (f : EnvelopingBalancedTensorSpace k R M P →ₗ[Rᵐᵒᵖ] X) (p : P) (x : M),
      envelopingBalancedTensorCurry k R M P X f p x=
        f (balancedTensorTmul k R M P x p) := by
  intros
  rfl

noncomputable def envelopingBalancedTensorHomRestrictMap :
    letI := envelopingLeftModule k R P
    letI := envelopingBalancedTensorHomModule k R M X
    (P →ₗ[AlgebraEnvelopingRing k R] BalancedTensorHom k R M X) →
      (P →ₗ[R] BalancedTensorHom k R M X) := by
  letI := envelopingLeftModule k R P
  letI := envelopingBalancedTensorHomModule k R M X
  intro g
  exact {
    toFun := g
    map_add' := g.map_add
    map_smul' := fun a p => by
      apply balancedTensorHom_ext k R M X
      intro x
      have h := g.map_smul ((Algebra.TensorProduct.includeLeft : R →ₐ[k]
        AlgebraEnvelopingRing k R) a) p
      have hx := congrArg (fun f : BalancedTensorHom k R M X => f x) h
      simpa only [Algebra.TensorProduct.includeLeft_apply,
        envelopingBalancedTensorHomModule_tmul_apply,one_smul,
        balancedTensorHom_smul_apply] using hx}

noncomputable def envelopingBalancedTensorUncurry :
    letI := envelopingBalancedTensorRightModule k R M P
    letI := envelopingBalancedTensorHomModule k R M X
    (P →ₗ[AlgebraEnvelopingRing k R] BalancedTensorHom k R M X) →
      (EnvelopingBalancedTensorSpace k R M P →ₗ[Rᵐᵒᵖ] X) := by
  letI := envelopingLeftModule k R P
  letI := envelopingLeftScalarTower k R P
  letI := envelopingRightModule k R P
  letI := envelopingBalancedTensorRightModule k R M P
  letI := envelopingBalancedTensorHomModule k R M X
  intro g
  let gR := envelopingBalancedTensorHomRestrictMap k R M P X g
  let f := balancedTensorUncurry k R M P X gR
  exact {
    toFun := f
    map_add' := f.map_add
    map_smul' := fun b t => by
      refine balancedTensorSpace_induction k R M P
        (fun t => f (b • t)=b • f t) ?_ ?_ ?_ t
      · simp only [smul_zero,map_zero]
      · intro x p
        rw [envelopingBalancedTensorRightModule_tmul]
        change balancedTensorUncurry k R M P X gR (balancedTensorTmul k R M P x (b • p))=
          b • balancedTensorUncurry k R M P X gR (balancedTensorTmul k R M P x p)
        rw [balancedTensorUncurry_tmul,balancedTensorUncurry_tmul]
        change g (b • p) x=b • g p x
        have h := g.map_smul ((Algebra.TensorProduct.includeRight : Rᵐᵒᵖ →ₐ[k]
          AlgebraEnvelopingRing k R) b) p
        have hx := congrArg (fun f : BalancedTensorHom k R M X => f x) h
        simpa only [Algebra.TensorProduct.includeRight_apply,
          envelopingBalancedTensorHomModule_tmul_apply,MulOpposite.op_one,one_smul] using hx
      · intro a c ha hc
        simp only [smul_add,map_add,ha,hc]}

theorem envelopingBalancedTensorUncurry_tmul :
    letI := envelopingLeftModule k R P
    letI := envelopingBalancedTensorRightModule k R M P
    letI := envelopingBalancedTensorHomModule k R M X
    ∀ (g : P →ₗ[AlgebraEnvelopingRing k R] BalancedTensorHom k R M X) (x : M) (p : P),
      envelopingBalancedTensorUncurry k R M P X g (balancedTensorTmul k R M P x p)=g p x := by
  letI := envelopingLeftModule k R P
  letI := envelopingLeftScalarTower k R P
  intro g x p
  exact balancedTensorUncurry_tmul k R M P X
    (envelopingBalancedTensorHomRestrictMap k R M P X g) x p

end ASGinzburg
