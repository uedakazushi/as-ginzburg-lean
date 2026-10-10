import ASGinzburg.AlgebraEnvelopingTensorRightModule

/-! Genuine maps of right enveloping modules on tensors of ordinary
right and left modules, with identity and composition laws. -/
namespace ASGinzburg
open scoped TensorProduct
universe u v w w' w'' z z' z''
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable {M : Type w} [AddCommGroup M] [Module k M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k Rᵐᵒᵖ M]
variable {M' : Type w'} [AddCommGroup M'] [Module k M'] [Module Rᵐᵒᵖ M']
  [IsScalarTower k Rᵐᵒᵖ M']
variable {N : Type z} [AddCommGroup N] [Module k N] [Module R N]
  [IsScalarTower k R N]
variable {N' : Type z'} [AddCommGroup N'] [Module k N'] [Module R N']
  [IsScalarTower k R N']

attribute [local instance] tensorRightEnvelopingModule

noncomputable def tensorRightEnvelopingMap (f : M →ₗ[Rᵐᵒᵖ] M') (g : N →ₗ[R] N') :
    (M ⊗[k] N) →ₗ[(AlgebraEnvelopingRing k R)ᵐᵒᵖ] (M' ⊗[k] N') where
  toFun := TensorProduct.map (f.restrictScalars k) (g.restrictScalars k)
  map_add' := map_add _
  map_smul' e x := by
    change TensorProduct.map (f.restrictScalars k) (g.restrictScalars k) (e • x) =
      e • TensorProduct.map (f.restrictScalars k) (g.restrictScalars k) x
    obtain ⟨e, rfl⟩ := MulOpposite.op_surjective e
    induction e using TensorProduct.inductionOn with
    | tmul a b =>
        induction x using TensorProduct.inductionOn with
        | tmul m n =>
            change TensorProduct.map (f.restrictScalars k) (g.restrictScalars k)
              (MulOpposite.op (a ⊗ₜ[k] MulOpposite.op b.unop) • (m ⊗ₜ[k] n)) =
                MulOpposite.op (a ⊗ₜ[k] MulOpposite.op b.unop) •
                  TensorProduct.map (f.restrictScalars k) (g.restrictScalars k) (m ⊗ₜ[k] n)
            rw [tensorRightEnvelopingModule_tmul_smul, TensorProduct.map_tmul,
              TensorProduct.map_tmul, tensorRightEnvelopingModule_tmul_smul]
            simp only [LinearMap.restrictScalars_apply, map_smul]
        | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | add e h he hh => simp only [MulOpposite.op_add, add_smul, map_add, he, hh]

theorem tensorRightEnvelopingMap_apply (f : M →ₗ[Rᵐᵒᵖ] M') (g : N →ₗ[R] N')
    (x : M ⊗[k] N) :
    tensorRightEnvelopingMap k R f g x =
      TensorProduct.map (f.restrictScalars k) (g.restrictScalars k) x := rfl

theorem tensorRightEnvelopingMap_tmul (f : M →ₗ[Rᵐᵒᵖ] M') (g : N →ₗ[R] N')
    (m : M) (n : N) :
    tensorRightEnvelopingMap k R f g (m ⊗ₜ[k] n) = f m ⊗ₜ[k] g n := by
  exact TensorProduct.map_tmul (f.restrictScalars k) (g.restrictScalars k) m n

theorem tensorRightEnvelopingMap_id :
    tensorRightEnvelopingMap k R (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M)
      (LinearMap.id : N →ₗ[R] N) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  change TensorProduct.map LinearMap.id LinearMap.id x = x
  rw [TensorProduct.map_id]
  rfl

variable {M'' : Type w''} [AddCommGroup M''] [Module k M''] [Module Rᵐᵒᵖ M'']
  [IsScalarTower k Rᵐᵒᵖ M'']
variable {N'' : Type z''} [AddCommGroup N''] [Module k N''] [Module R N'']
  [IsScalarTower k R N'']

theorem tensorRightEnvelopingMap_comp (f : M →ₗ[Rᵐᵒᵖ] M') (f' : M' →ₗ[Rᵐᵒᵖ] M'')
    (g : N →ₗ[R] N') (g' : N' →ₗ[R] N'') :
    tensorRightEnvelopingMap k R (f'.comp f) (g'.comp g) =
      (tensorRightEnvelopingMap k R f' g').comp (tensorRightEnvelopingMap k R f g) := by
  apply LinearMap.ext
  intro x
  change TensorProduct.map ((f'.comp f).restrictScalars k) ((g'.comp g).restrictScalars k) x =
    TensorProduct.map (f'.restrictScalars k) (g'.restrictScalars k)
      (TensorProduct.map (f.restrictScalars k) (g.restrictScalars k) x)
  rw [LinearMap.restrictScalars_comp, LinearMap.restrictScalars_comp, TensorProduct.map_comp]
  rfl

end ASGinzburg
