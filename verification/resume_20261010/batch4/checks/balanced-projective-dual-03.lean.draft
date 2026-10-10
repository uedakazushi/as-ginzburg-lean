import ASGinzburg.BalancedTensorAdjunction
import ASGinzburg.BalancedTensorSwapNaturality
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.Exact

/-! Tensoring with a projective right module preserves injections. The proof
uses the actual balanced quotient: a functional on the source tensor extends
by projective lifting along restriction of vector-space duals. -/
namespace ASGinzburg
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v w z z'
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module Rᵐᵒᵖ M]
variable [IsScalarTower k Rᵐᵒᵖ M]
variable (N : Type z) [AddCommGroup N] [Module k N] [Module R N]
variable [IsScalarTower k R N]
variable (N' : Type z') [AddCommGroup N'] [Module k N'] [Module R N']
variable [IsScalarTower k R N']

noncomputable def balancedTensorDualCurry
    (f : BalancedTensorSpace k R M N →ₗ[k] k) :
    letI := balancedTensorDoubleOppositeModule R N
    letI := balancedTensorDoubleOppositeIsScalarTower k R N
    M →ₗ[Rᵐᵒᵖ] BalancedTensorHom k Rᵐᵒᵖ N k := by
  letI := balancedTensorDoubleOppositeModule R N
  letI := balancedTensorDoubleOppositeIsScalarTower k R N
  exact
    { toFun := fun x => (balancedTensorHomLinearEquiv k Rᵐᵒᵖ N k).symm
        (f.comp (balancedTensorBilinear k R M N x))
      map_add' := fun x y => by
        apply balancedTensorHom_ext k Rᵐᵒᵖ N k
        intro a
        change f (balancedTensorBilinear k R M N (x+y) a) =
          f (balancedTensorBilinear k R M N x a) +
          f (balancedTensorBilinear k R M N y a)
        rw [map_add, LinearMap.add_apply, map_add]
      map_smul' := fun r x => by
        apply balancedTensorHom_ext k Rᵐᵒᵖ N k
        intro y
        change f (balancedTensorTmul k R M N (r • x) y) =
          f (balancedTensorTmul k R M N x (MulOpposite.unop r • y))
        simpa only [MulOpposite.op_unop] using congrArg f
          (balancedTensorTmul_balance k R M N (MulOpposite.unop r) x y) }

omit [IsScalarTower k Rᵐᵒᵖ M] in
theorem balancedTensorDualCurry_apply
    (f : BalancedTensorSpace k R M N →ₗ[k] k) (x : M) (y : N) :
    balancedTensorDualCurry k R M N f x y =
      f (balancedTensorTmul k R M N x y) := rfl

noncomputable def balancedTensorDualRestrict (g : N →ₗ[R] N') :
    letI := balancedTensorDoubleOppositeModule R N
    letI := balancedTensorDoubleOppositeIsScalarTower k R N
    letI := balancedTensorDoubleOppositeModule R N'
    letI := balancedTensorDoubleOppositeIsScalarTower k R N'
    BalancedTensorHom k Rᵐᵒᵖ N' k →ₗ[Rᵐᵒᵖ] BalancedTensorHom k Rᵐᵒᵖ N k := by
  letI := balancedTensorDoubleOppositeModule R N
  letI := balancedTensorDoubleOppositeIsScalarTower k R N
  letI := balancedTensorDoubleOppositeModule R N'
  letI := balancedTensorDoubleOppositeIsScalarTower k R N'
  exact
    { toFun := fun f => (balancedTensorHomLinearEquiv k Rᵐᵒᵖ N k).symm
        ((balancedTensorHomLinearEquiv k Rᵐᵒᵖ N' k f).comp (g.restrictScalars k))
      map_add' := fun f h => by
        apply balancedTensorHom_ext k Rᵐᵒᵖ N k
        intro y
        rfl
      map_smul' := fun r f => by
        apply balancedTensorHom_ext k Rᵐᵒᵖ N k
        intro y
        change f (MulOpposite.unop r • g y) = f (g (MulOpposite.unop r • y))
        rw [g.map_smul] }

theorem balancedTensorDualRestrict_apply (g : N →ₗ[R] N')
    (f : BalancedTensorHom k Rᵐᵒᵖ N' k) (y : N) :
    balancedTensorDualRestrict k R N N' g f y = f (g y) := rfl

theorem balancedTensorDualRestrict_surjective (g : N →ₗ[R] N')
    (hg : Function.Injective g) :
    Function.Surjective (balancedTensorDualRestrict k R N N' g) := by
  letI := balancedTensorDoubleOppositeModule R N
  letI := balancedTensorDoubleOppositeIsScalarTower k R N
  letI := balancedTensorDoubleOppositeModule R N'
  letI := balancedTensorDoubleOppositeIsScalarTower k R N'
  intro f
  obtain ⟨h, hh⟩ := LinearMap.dualMap_surjective_of_injective
    (f := g.restrictScalars k) hg (balancedTensorHomLinearEquiv k Rᵐᵒᵖ N k f)
  refine ⟨(balancedTensorHomLinearEquiv k Rᵐᵒᵖ N' k).symm h, ?_⟩
  apply balancedTensorHom_ext k Rᵐᵒᵖ N k
  intro y
  exact LinearMap.congr_fun hh y

noncomputable def balancedTensorDualUncurry
    (g : letI := balancedTensorDoubleOppositeModule R N
      letI := balancedTensorDoubleOppositeIsScalarTower k R N
      M →ₗ[Rᵐᵒᵖ] BalancedTensorHom k Rᵐᵒᵖ N k) :
    BalancedTensorSpace k R M N →ₗ[k] k := by
  letI := balancedTensorDoubleOppositeModule R N
  letI := balancedTensorDoubleOppositeIsScalarTower k R N
  exact (balancedTensorUncurry k Rᵐᵒᵖ N M k g).comp
    (balancedTensorSwapMap k R M N)

theorem balancedTensorDualUncurry_tmul
    (g : letI := balancedTensorDoubleOppositeModule R N
      letI := balancedTensorDoubleOppositeIsScalarTower k R N
      M →ₗ[Rᵐᵒᵖ] BalancedTensorHom k Rᵐᵒᵖ N k) (x : M) (y : N) :
    balancedTensorDualUncurry k R M N g (balancedTensorTmul k R M N x y) = g x y := by
  letI := balancedTensorDoubleOppositeModule R N
  letI := balancedTensorDoubleOppositeIsScalarTower k R N
  unfold balancedTensorDualUncurry
  rw [LinearMap.comp_apply, balancedTensorSwapMap_tmul]
  exact balancedTensorUncurry_tmul k Rᵐᵒᵖ N M k g y x

theorem balancedTensorFunctional_exists_extension [Module.Projective Rᵐᵒᵖ M]
    (g : N →ₗ[R] N') (hg : Function.Injective g)
    (f : BalancedTensorSpace k R M N →ₗ[k] k) :
    ∃ h : BalancedTensorSpace k R M N' →ₗ[k] k,
      h.comp (balancedTensorMapRight k R M g) = f := by
  letI := balancedTensorDoubleOppositeModule R N
  letI := balancedTensorDoubleOppositeIsScalarTower k R N
  letI := balancedTensorDoubleOppositeModule R N'
  letI := balancedTensorDoubleOppositeIsScalarTower k R N'
  obtain ⟨h, hh⟩ := Module.projective_lifting_property
    (balancedTensorDualRestrict k R N N' g) (balancedTensorDualCurry k R M N f)
    (balancedTensorDualRestrict_surjective k R N N' g hg)
  refine ⟨balancedTensorDualUncurry k R M N' h, ?_⟩
  apply balancedTensorSpace_linearMap_ext k R M N
  intro x y
  rw [LinearMap.comp_apply, balancedTensorMapRight_tmul, balancedTensorDualUncurry_tmul]
  have hx := LinearMap.congr_fun hh x
  have hxy := congrArg (fun a : BalancedTensorHom k Rᵐᵒᵖ N k => a y) hx
  simpa only [LinearMap.comp_apply, balancedTensorDualRestrict_apply,
    balancedTensorDualCurry_apply] using hxy

theorem balancedTensorMapRight_injective_of_projective [Module.Projective Rᵐᵒᵖ M]
    (g : N →ₗ[R] N') (hg : Function.Injective g) :
    Function.Injective (balancedTensorMapRight k R M g) := by
  apply LinearMap.dualMap_surjective_iff.mp
  intro f
  obtain ⟨h, hh⟩ := balancedTensorFunctional_exists_extension k R M N N' g hg f
  exact ⟨h, hh⟩

instance balancedTensorRightFunctorPreservesMonomorphisms [Module.Projective Rᵐᵒᵖ M] :
    (balancedTensorRightFunctor.{u,v,w,z} k R M).PreservesMonomorphisms where
  preserves g hg := by
    apply (ModuleCat.mono_iff_injective _).mpr
    exact balancedTensorMapRight_injective_of_projective k R M _ _ g.hom
      ((ModuleCat.mono_iff_injective g).mp hg)

instance balancedTensorRightFunctorPreservesHomology [Module.Projective Rᵐᵒᵖ M] :
    (balancedTensorRightFunctor.{u,v,w,max w z} k R M).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels _

theorem balancedTensorRightFunctor_map_exact [Module.Projective Rᵐᵒᵖ M]
    (S : ShortComplex (ModuleCat.{max w z} R)) (hS : S.Exact) :
    (S.map (balancedTensorRightFunctor.{u,v,w,max w z} k R M)).Exact :=
  hS.map _

end ASGinzburg
