import ASGinzburg.EnvelopingBalancedTensorHomEquiv
import ASGinzburg.EnvelopingBalancedTensorHomMaps

/-! Over a field, tensoring an actual projective enveloping module
with any right R module produces a projective right R module. -/
namespace ASGinzburg
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module Rᵐᵒᵖ M]
variable [IsScalarTower k Rᵐᵒᵖ M]
variable (P : Type z) [AddCommGroup P] [Module k P]
variable [Module (AlgebraEnvelopingRing k R) P] [IsScalarTower k (AlgebraEnvelopingRing k R) P]

theorem envelopingBalancedTensor_projective [Module.Projective (AlgebraEnvelopingRing k R) P] :
    letI := envelopingBalancedTensorRightModule k R M P
    Module.Projective Rᵐᵒᵖ (EnvelopingBalancedTensorSpace k R M P) := by
  letI := envelopingLeftModule k R P
  letI := envelopingBalancedTensorRightModule k R M P
  letI := envelopingBalancedTensorRightScalarTower k R M P
  let T := EnvelopingBalancedTensorSpace k R M P
  refine Module.Projective.of_lifting_property'' fun f hf => ?_
  letI := envelopingBalancedTensorHomModule k R M T
  letI := envelopingBalancedTensorHomModule k R M (T →₀ Rᵐᵒᵖ)
  let Hf := envelopingBalancedTensorHomMap k R M f
  let g := envelopingBalancedTensorCurry k R M P T (LinearMap.id)
  obtain ⟨h,hh⟩ := Module.projective_lifting_property Hf g
    (envelopingBalancedTensorHomMap_surjective k R M f hf)
  refine ⟨envelopingBalancedTensorUncurry k R M P (T →₀ Rᵐᵒᵖ) h,?_⟩
  apply LinearMap.ext
  intro t
  refine balancedTensorSpace_induction k R M P
    (fun t => (f.comp (envelopingBalancedTensorUncurry k R M P (T →₀ Rᵐᵒᵖ) h)) t=
      LinearMap.id t) ?_ ?_ ?_ t
  · simp only [map_zero]
  · intro x p
    change f (envelopingBalancedTensorUncurry k R M P (T →₀ Rᵐᵒᵖ) h
      (balancedTensorTmul k R M P x p))=balancedTensorTmul k R M P x p
    rw [envelopingBalancedTensorUncurry_tmul]
    have hp := congrArg (fun e : P →ₗ[AlgebraEnvelopingRing k R]
      BalancedTensorHom k R M T => e p) hh
    have hpx := congrArg (fun e : BalancedTensorHom k R M T => e x) hp
    exact hpx
  · intro a b ha hb
    simp only [map_add,ha,hb]

end ASGinzburg
