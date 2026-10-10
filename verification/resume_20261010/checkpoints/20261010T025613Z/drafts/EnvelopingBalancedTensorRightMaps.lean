import work.ASGinzburgDraft.EnvelopingBalancedTensorRightAction
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-! The residual right action is compatible with the base field, and
actual enveloping-linear maps induce genuine right-module maps. -/
namespace ASGinzburg
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v w z z'
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module Rᵐᵒᵖ M]
variable (P : Type z) [AddCommGroup P] [Module k P]
variable [Module (AlgebraEnvelopingRing k R) P] [IsScalarTower k (AlgebraEnvelopingRing k R) P]

noncomputable def envelopingBalancedTensorRightScalarTower :
    letI := envelopingBalancedTensorRightModule k R M P
    IsScalarTower k Rᵐᵒᵖ (EnvelopingBalancedTensorSpace k R M P) := by
  letI := envelopingLeftModule k R P
  letI := envelopingRightModule k R P
  letI := envelopingRightScalarTower k R P
  letI := envelopingBalancedTensorRightModule k R M P
  constructor
  intro c b t
  refine balancedTensorSpace_induction k R M P
    (fun t => (c • b) • t=c • b • t) ?_ ?_ ?_ t
  · simp only [smul_zero]
  · intro x y
    rw [envelopingBalancedTensorRightModule_tmul,
      envelopingBalancedTensorRightModule_tmul,smul_assoc]
    exact (balancedTensorBilinear k R M P x).map_smul c (b • y)
  · intro a b ha hb
    simp only [smul_add,ha,hb]

variable {P} {P' : Type z'} [AddCommGroup P'] [Module k P']
variable [Module (AlgebraEnvelopingRing k R) P'] [IsScalarTower k (AlgebraEnvelopingRing k R) P']

noncomputable def envelopingBalancedTensorRightMap
    (f : P →ₗ[AlgebraEnvelopingRing k R] P') :
    letI := envelopingBalancedTensorRightModule k R M P
    letI := envelopingBalancedTensorRightModule k R M P'
    EnvelopingBalancedTensorSpace k R M P →ₗ[Rᵐᵒᵖ]
      EnvelopingBalancedTensorSpace k R M P' := by
  letI := envelopingLeftModule k R P
  letI := envelopingLeftModule k R P'
  letI := envelopingLeftScalarTower k R P
  letI := envelopingLeftScalarTower k R P'
  letI := envelopingRightModule k R P
  letI := envelopingRightModule k R P'
  letI := envelopingBalancedTensorRightModule k R M P
  letI := envelopingBalancedTensorRightModule k R M P'
  let g := balancedTensorMapRight k R M (envelopingLeftLinearMap k R f)
  exact {
    toFun := g
    map_add' := g.map_add
    map_smul' := fun b t => by
      refine balancedTensorSpace_induction k R M P
        (fun t => g (b • t)=b • g t) ?_ ?_ ?_ t
      · simp only [smul_zero,map_zero]
      · intro x y
        rw [envelopingBalancedTensorRightModule_tmul]
        change balancedTensorMapRight k R M (envelopingLeftLinearMap k R f)
          (balancedTensorTmul k R M P x (b • y))=b •
          balancedTensorMapRight k R M (envelopingLeftLinearMap k R f)
            (balancedTensorTmul k R M P x y)
        rw [balancedTensorMapRight_tmul,balancedTensorMapRight_tmul,
          envelopingBalancedTensorRightModule_tmul]
        exact congrArg (balancedTensorTmul k R M P' x)
          (envelopingLinearMap_right_smul k R f b y)
      · intro a c ha hc
        simp only [smul_add,map_add,ha,hc]}

theorem envelopingBalancedTensorRightMap_tmul
    (f : P →ₗ[AlgebraEnvelopingRing k R] P') (x : M) (y : P) :
    letI := envelopingLeftModule k R P
    letI := envelopingLeftModule k R P'
    envelopingBalancedTensorRightMap k R M f (balancedTensorTmul k R M P x y)=
      balancedTensorTmul k R M P' x (f y) := by
  letI := envelopingLeftModule k R P
  letI := envelopingLeftModule k R P'
  letI := envelopingLeftScalarTower k R P
  letI := envelopingLeftScalarTower k R P'
  exact balancedTensorMapRight_tmul k R M (envelopingLeftLinearMap k R f) x y

noncomputable def envelopingBalancedTensorRightFunctor :
    ModuleCat.{z} (AlgebraEnvelopingRing k R) ⥤ ModuleCat.{max w z} Rᵐᵒᵖ where
  obj P := by
    letI := envelopingBalancedTensorRightModule k R M P
    exact ModuleCat.of Rᵐᵒᵖ (EnvelopingBalancedTensorSpace k R M P)
  map {P P'} f := by
    letI := envelopingBalancedTensorRightModule k R M P
    letI := envelopingBalancedTensorRightModule k R M P'
    exact ModuleCat.ofHom (envelopingBalancedTensorRightMap k R M f.hom)
  map_id P := by
    letI := envelopingBalancedTensorRightModule k R M P
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    letI := envelopingLeftModule k R P
    letI := envelopingLeftScalarTower k R P
    change balancedTensorMapRight k R M (envelopingLeftLinearMap k R (LinearMap.id)) t=t
    have h : envelopingLeftLinearMap k R (LinearMap.id (M := P))=LinearMap.id := rfl
    rw [h,balancedTensorMapRight_id]
    rfl
  map_comp {P P' P''} f g := by
    letI := envelopingBalancedTensorRightModule k R M P
    letI := envelopingBalancedTensorRightModule k R M P'
    letI := envelopingBalancedTensorRightModule k R M P''
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    letI := envelopingLeftModule k R P
    letI := envelopingLeftModule k R P'
    letI := envelopingLeftModule k R P''
    letI := envelopingLeftScalarTower k R P
    letI := envelopingLeftScalarTower k R P'
    letI := envelopingLeftScalarTower k R P''
    exact congrArg (fun h => h t)
      (balancedTensorMapRight_comp k R M
        (envelopingLeftLinearMap k R f.hom) (envelopingLeftLinearMap k R g.hom))

instance envelopingBalancedTensorRightFunctorAdditive :
    (envelopingBalancedTensorRightFunctor.{u,v,w,z} k R M).Additive where
  map_add := by
    intro P P' f g
    letI := envelopingBalancedTensorRightModule k R M P
    letI := envelopingBalancedTensorRightModule k R M P'
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    letI := envelopingLeftModule k R P
    letI := envelopingLeftModule k R P'
    letI := envelopingLeftScalarTower k R P
    letI := envelopingLeftScalarTower k R P'
    exact congrArg (fun h => h t) (balancedTensorMapRight_add k R M
      (envelopingLeftLinearMap k R f.hom) (envelopingLeftLinearMap k R g.hom))

end ASGinzburg
