import ASGinzburg.AlgebraEnvelopingTensorFinsuppFree
import ASGinzburg.AlgebraEnvelopingTensorRightMaps

/-! Projective right and left modules tensor to an actual projective
right enveloping module. The proof uses their genuine free-module
splittings, the free tensor identification, and actual tensor maps. -/
namespace ASGinzburg
open scoped TensorProduct
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]

attribute [local instance] tensorRightEnvelopingModule
attribute [local instance 2000] Semiring.toModule

noncomputable def rightRegularUnopLinearEquiv : Rᵐᵒᵖ ≃ₗ[Rᵐᵒᵖ] R where
  toFun := MulOpposite.unop
  invFun := MulOpposite.op
  left_inv := MulOpposite.op_unop
  right_inv := MulOpposite.unop_op
  map_add' := MulOpposite.unop_add
  map_smul' r x := by
    change MulOpposite.unop (r*x) = x.unop*r.unop
    rfl

variable (M : Type w) [AddCommGroup M] [Module k M] [Module Rᵐᵒᵖ M]
variable (N : Type z) [AddCommGroup N] [Module k N] [Module R N]
variable [IsScalarTower k Rᵐᵒᵖ M] [IsScalarTower k R N]

theorem tensorRightEnvelopingModule_projective
    [Module.Projective Rᵐᵒᵖ M] [Module.Projective R N] :
    Module.Projective (AlgebraEnvelopingRing k R)ᵐᵒᵖ (M ⊗[k] N) := by
  obtain ⟨sM, hsM⟩ := (inferInstance : Module.Projective Rᵐᵒᵖ M)
  obtain ⟨sN, hsN⟩ := (inferInstance : Module.Projective R N)
  let eM : (M →₀ Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] (M →₀ R) :=
    Finsupp.mapRange.linearEquiv (rightRegularUnopLinearEquiv R)
  let iM : M →ₗ[Rᵐᵒᵖ] (M →₀ R) := eM.toLinearMap.comp sM
  let pM : (M →₀ R) →ₗ[Rᵐᵒᵖ] M :=
    (Finsupp.linearCombination Rᵐᵒᵖ (id : M → M)).comp eM.symm.toLinearMap
  let pN : (N →₀ R) →ₗ[R] N := Finsupp.linearCombination R (id : N → N)
  have hM : pM.comp iM = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change Finsupp.linearCombination Rᵐᵒᵖ (id : M → M) (eM.symm (eM (sM x))) = x
    rw [eM.symm_apply_apply]
    exact hsM x
  have hN : pN.comp sN = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact hsN x
  letI := tensorRightEnvelopingFinsupp_projective k R M N
  apply Module.Projective.of_split
    (tensorRightEnvelopingMap k R iM sN) (tensorRightEnvelopingMap k R pM pN)
  rw [← tensorRightEnvelopingMap_comp, hM, hN, tensorRightEnvelopingMap_id]

end ASGinzburg
