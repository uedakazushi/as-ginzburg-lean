import work.ASGinzburgDraft.OrdinaryModuleRingDual
import ASGinzburg.BalancedTensorLeftFunctor

/-! The genuine noncommutative tensor evaluation map. The ring dual is
a right R module, and the target is Hom_R(P,N) with its scalar-field
module structure. Evaluation is natural in the source module. -/
namespace ASGinzburg
open CategoryTheory Opposite
open scoped ModuleCat.Algebra
universe u v
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (N : ModuleCat.{v} R)

noncomputable def ordinaryRingDualTensorModuleK (P : ModuleCat.{v} R) :
    Module k (ordinaryRingDual R P) :=
  Module.compHom _ (algebraMap k Rᵐᵒᵖ)

attribute [local instance 2100] ordinaryRingDualTensorModuleK

noncomputable def ordinaryRingDualTensorScalarTower (P : ModuleCat.{v} R) :
    letI := ordinaryRingDualTensorModuleK k R P
    letI : SMul k (ordinaryRingDual R P) :=
      (ordinaryRingDualTensorModuleK k R P).toSMul
    IsScalarTower k Rᵐᵒᵖ (ordinaryRingDual R P) := by
  letI := ordinaryRingDualTensorModuleK k R P
  letI : SMul k (ordinaryRingDual R P) :=
    (ordinaryRingDualTensorModuleK k R P).toSMul
  constructor
  intro c b f
  change (c • b) • f = (algebraMap k Rᵐᵒᵖ c) • (b • f)
  rw [Algebra.smul_def, mul_smul]

attribute [local instance 2100] ordinaryRingDualTensorScalarTower

noncomputable def ordinaryRingDualTensorEvaluationBilinear (P : ModuleCat.{v} R) :
    ordinaryRingDual R P →ₗ[k] N →ₗ[k] (P →ₗ[R] N) where
  toFun f :=
    { toFun := fun y =>
        { toFun := fun x => f x • y
          map_add' := fun x z => by rw [f.map_add, add_smul]
          map_smul' := fun a x => by rw [f.map_smul]; exact mul_smul a (f x) y }
      map_add' := fun y z => by ext x; exact smul_add (f x) y z
      map_smul' := fun c y => by ext x; exact smul_comm (f x) c y }
  map_add' := fun f g => by ext y x; exact add_smul (f x) (g x) y
  map_smul' := fun c f => by
    ext y x
    change (((algebraMap k Rᵐᵒᵖ c) • f) x) • y = c • (f x • y)
    rw [ordinaryRingDual_smul_apply, MulOpposite.algebraMap_apply,
      MulOpposite.unop_op, ← Algebra.commutes c (f x), ← Algebra.smul_def, smul_assoc]

noncomputable def ordinaryRingDualTensorEvaluation (P : ModuleCat.{v} R) :
    BalancedTensorSpace k R (ordinaryRingDual R P) N →ₗ[k] (P →ₗ[R] N) :=
  balancedTensorLift k R (ordinaryRingDual R P) N
    (ordinaryRingDualTensorEvaluationBilinear k R N P) (by
      intro a f y
      apply LinearMap.ext
      intro x
      change (f x * a) • y = f x • (a • y)
      exact mul_smul (f x) a y)

@[simp] theorem ordinaryRingDualTensorEvaluation_tmul (P : ModuleCat.{v} R)
    (f : ordinaryRingDual R P) (y : N) (x : P) :
    ordinaryRingDualTensorEvaluation k R N P
      (balancedTensorTmul k R (ordinaryRingDual R P) N f y) x = f x • y := by
  rw [ordinaryRingDualTensorEvaluation, balancedTensorLift_tmul]
  rfl

noncomputable def ordinaryRingHomFunctor : (ModuleCat.{v} R)ᵒᵖ ⥤ ModuleCat.{v} k where
  obj P := ModuleCat.of k (P.unop →ₗ[R] N)
  map f := ModuleCat.ofHom
    { toFun := fun g => g.comp f.unop.hom
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_id P := by
    apply ModuleCat.hom_ext
    ext g x
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    ext h x
    rfl

noncomputable def ordinaryRingDualTensorEvaluationNatTrans :
    (ordinaryRingDualFunctor R) ⋙ balancedTensorLeftFunctor k R N ⟶
      ordinaryRingHomFunctor k R N where
  app P := ModuleCat.ofHom (ordinaryRingDualTensorEvaluation k R N P.unop)
  naturality {P Q} f := by
    letI := ordinaryRingDualTensorModuleK k R P.unop
    letI := ordinaryRingDualTensorModuleK k R Q.unop
    letI : SMul k (ordinaryRingDual R P.unop) :=
      (ordinaryRingDualTensorModuleK k R P.unop).toSMul
    letI : SMul k (ordinaryRingDual R Q.unop) :=
      (ordinaryRingDualTensorModuleK k R Q.unop).toSMul
    letI := ordinaryRingDualTensorScalarTower k R P.unop
    letI := ordinaryRingDualTensorScalarTower k R Q.unop
    apply ModuleCat.hom_ext
    apply balancedTensorSpace_linearMap_ext
    intro g y
    apply LinearMap.ext
    intro x
    change ordinaryRingDualTensorEvaluation k R N Q.unop
        (balancedTensorMapLeft k R N (ordinaryRingDualMap R f.unop)
          (balancedTensorTmul k R (ordinaryRingDual R P.unop) N g y)) x =
      ordinaryRingDualTensorEvaluation k R N P.unop
        (balancedTensorTmul k R (ordinaryRingDual R P.unop) N g y) (f.unop x)
    rw [balancedTensorMapLeft_tmul, ordinaryRingDualTensorEvaluation_tmul,
      ordinaryRingDualTensorEvaluation_tmul, ordinaryRingDualMap_apply]

end ASGinzburg
