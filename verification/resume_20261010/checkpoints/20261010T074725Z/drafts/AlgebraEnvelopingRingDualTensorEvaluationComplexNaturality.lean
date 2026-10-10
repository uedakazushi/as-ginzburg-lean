import work.ASGinzburgDraft.AlgebraEnvelopingRingDualTensorEvaluationComplex

/-! Naturality for the actual tensor functor, including its canonical
field action, and the resulting comparison of actual Hom complexes. -/
namespace ASGinzburg
open CategoryTheory Opposite
open scoped ModuleCat.Algebra
universe u v t
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : ModuleCat.{v} Rᵐᵒᵖ)
attribute [local instance 2100] ordinaryRingDualTensorModuleK
attribute [local instance 2100] ordinaryRingDualTensorScalarTower
attribute [local instance 3500] ordinaryRingDualTensorFieldSMulK
variable {P Q : ModuleCat.{v} (AlgebraEnvelopingRing k R)}

set_option maxHeartbeats 1000000 in
@[simp] theorem envelopingRingDualTensorEvaluationSource_map_tmul (g : P ⟶ Q)
    (f : ordinaryRingDual (AlgebraEnvelopingRing k R) Q)
    (φ : BalancedTensorHom k R M k) :
    (envelopingRingDualTensorEvaluationSourceFunctor k R M).map g.op
        (envelopingRingDualTensorEvaluationCanonicalTmul k R M Q f φ) =
      envelopingRingDualTensorEvaluationCanonicalTmul k R M P
        (envelopingRingDualRestrictedMap k R g f) φ := by
  letI := envelopingTensorEvaluationRestrictedRightModule k R
    (ordinaryRingDual (AlgebraEnvelopingRing k R) P)
  letI := envelopingTensorEvaluationRestrictedRightModule k R
    (ordinaryRingDual (AlgebraEnvelopingRing k R) Q)
  letI : Module k (ordinaryRingDual (AlgebraEnvelopingRing k R) P) :=
    Module.compHom _ (algebraMap k Rᵐᵒᵖ)
  letI : Module k (ordinaryRingDual (AlgebraEnvelopingRing k R) Q) :=
    Module.compHom _ (algebraMap k Rᵐᵒᵖ)
  letI : SMul k (ordinaryRingDual (AlgebraEnvelopingRing k R) P) :=
    (Module.compHom _ (algebraMap k Rᵐᵒᵖ)).toSMul
  letI : SMul k (ordinaryRingDual (AlgebraEnvelopingRing k R) Q) :=
    (Module.compHom _ (algebraMap k Rᵐᵒᵖ)).toSMul
  letI : IsScalarTower k Rᵐᵒᵖ (ordinaryRingDual (AlgebraEnvelopingRing k R) P) :=
    ⟨fun c a d => by
      change (c • a) • d = (algebraMap k Rᵐᵒᵖ c) • (a • d)
      rw [Algebra.smul_def, mul_smul]⟩
  letI : IsScalarTower k Rᵐᵒᵖ (ordinaryRingDual (AlgebraEnvelopingRing k R) Q) :=
    ⟨fun c a d => by
      change (c • a) • d = (algebraMap k Rᵐᵒᵖ c) • (a • d)
      rw [Algebra.smul_def, mul_smul]⟩
  change balancedTensorMapLeft k R (BalancedTensorHom k R M k)
      (envelopingRingDualRestrictedMap k R g)
      (balancedTensorTmul k R (ordinaryRingDual (AlgebraEnvelopingRing k R) Q)
        (BalancedTensorHom k R M k) f φ) =
    balancedTensorTmul k R (ordinaryRingDual (AlgebraEnvelopingRing k R) P)
      (BalancedTensorHom k R M k) (envelopingRingDualRestrictedMap k R g f) φ
  exact balancedTensorMapLeft_tmul k R (BalancedTensorHom k R M k)
    (envelopingRingDualRestrictedMap k R g) f φ

set_option maxHeartbeats 1600000 in
theorem envelopingRingDualTensorEvaluationSourceFieldIso_naturality (g : P ⟶ Q) :
    letI := envelopingTensorEvaluationRestrictedRightModule k R
      (ordinaryRingDual (AlgebraEnvelopingRing k R) P)
    letI := envelopingTensorEvaluationRestrictedRightModule k R
      (ordinaryRingDual (AlgebraEnvelopingRing k R) Q)
    letI := envelopingTensorEvaluationRestrictedRightScalarTower k R
      (ordinaryRingDual (AlgebraEnvelopingRing k R) P)
    letI := envelopingTensorEvaluationRestrictedRightScalarTower k R
      (ordinaryRingDual (AlgebraEnvelopingRing k R) Q)
    (envelopingRingDualTensorEvaluationSourceFunctor k R M).map g.op ≫
        (envelopingRingDualTensorEvaluationSourceFieldIso k R M P).hom =
      (envelopingRingDualTensorEvaluationSourceFieldIso k R M Q).hom ≫
        ModuleCat.ofHom (balancedTensorMapLeft k R (BalancedTensorHom k R M k)
          (envelopingRingDualRestrictedMap k R g)) := by
  letI := envelopingTensorEvaluationRestrictedRightModule k R
    (ordinaryRingDual (AlgebraEnvelopingRing k R) P)
  letI := envelopingTensorEvaluationRestrictedRightModule k R
    (ordinaryRingDual (AlgebraEnvelopingRing k R) Q)
  letI := envelopingTensorEvaluationRestrictedRightScalarTower k R
    (ordinaryRingDual (AlgebraEnvelopingRing k R) P)
  letI := envelopingTensorEvaluationRestrictedRightScalarTower k R
    (ordinaryRingDual (AlgebraEnvelopingRing k R) Q)
  letI : Module k (ordinaryRingDual (AlgebraEnvelopingRing k R) Q) :=
    Module.compHom _ (algebraMap k Rᵐᵒᵖ)
  letI : SMul k (ordinaryRingDual (AlgebraEnvelopingRing k R) Q) :=
    (Module.compHom _ (algebraMap k Rᵐᵒᵖ)).toSMul
  apply ModuleCat.hom_ext
  apply balancedTensorSpace_linearMap_ext
  intro f φ
  letI : Module k (ordinaryRingDual (AlgebraEnvelopingRing k R) Q) :=
    ordinaryRingDualTensorModuleK k (AlgebraEnvelopingRing k R) Q
  letI : SMul k (ordinaryRingDual (AlgebraEnvelopingRing k R) Q) :=
    ordinaryRingDualTensorFieldSMulK k (AlgebraEnvelopingRing k R) Q
  change (envelopingRingDualTensorEvaluationSourceFieldIso k R M P).hom
      ((envelopingRingDualTensorEvaluationSourceFunctor k R M).map g.op
        (envelopingRingDualTensorEvaluationCanonicalTmul k R M Q f φ)) =
    balancedTensorMapLeft k R (BalancedTensorHom k R M k)
      (envelopingRingDualRestrictedMap k R g)
      ((envelopingRingDualTensorEvaluationSourceFieldIso k R M Q).hom
        (envelopingRingDualTensorEvaluationCanonicalTmul k R M Q f φ))
  rw [envelopingRingDualTensorEvaluationSource_map_tmul,
    envelopingRingDualTensorEvaluationSourceFieldIso_tmul,
    envelopingRingDualTensorEvaluationSourceFieldIso_tmul,
    balancedTensorMapLeft_tmul]

variable [Module.Finite k M]

set_option maxHeartbeats 1600000 in
theorem envelopingFiniteProjectiveRingDualTensorTermIso_naturality
    (hP : ordinaryFiniteProjectiveProperty (AlgebraEnvelopingRing k R) P)
    (hQ : ordinaryFiniteProjectiveProperty (AlgebraEnvelopingRing k R) Q)
    (g : P ⟶ Q) :
    (envelopingRingDualTensorEvaluationSourceFunctor k R M).map g.op ≫
        (envelopingFiniteProjectiveRingDualTensorTermIso k R M P hP).hom =
      (envelopingFiniteProjectiveRingDualTensorTermIso k R M Q hQ).hom ≫
        (envelopingRingDualTensorEvaluationTargetFunctor k R M).map g.op := by
  letI := envelopingTensorEvaluationRestrictedRightModule k R
    (ordinaryRingDual (AlgebraEnvelopingRing k R) P)
  letI := envelopingTensorEvaluationRestrictedRightModule k R
    (ordinaryRingDual (AlgebraEnvelopingRing k R) Q)
  letI := envelopingTensorEvaluationRestrictedRightScalarTower k R
    (ordinaryRingDual (AlgebraEnvelopingRing k R) P)
  letI := envelopingTensorEvaluationRestrictedRightScalarTower k R
    (ordinaryRingDual (AlgebraEnvelopingRing k R) Q)
  letI := envelopingBalancedTensorRightModule k R M P
  letI := envelopingBalancedTensorRightModule k R M Q
  letI := envelopingBalancedTensorRightScalarTower k R M P
  letI := envelopingBalancedTensorRightScalarTower k R M Q
  let eP := envelopingFiniteProjectiveRingDualTensorEquiv k R M hP
  let eQ := envelopingFiniteProjectiveRingDualTensorEquiv k R M hQ
  let lP := eP.trans (ULift.moduleEquiv (R := k)).symm
  let lQ := eQ.trans (ULift.moduleEquiv (R := k)).symm
  have hn : ModuleCat.ofHom (balancedTensorMapLeft k R (BalancedTensorHom k R M k)
      (envelopingRingDualRestrictedMap k R g)) ≫ ModuleCat.ofHom lP.toLinearMap =
      ModuleCat.ofHom lQ.toLinearMap ≫
        (envelopingRingDualTensorEvaluationTargetFunctor k R M).map g.op := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply ULift.ext
    exact envelopingFiniteProjectiveRingDualTensorEquiv_naturality k R M hP hQ g z
  change _ ≫ ((envelopingRingDualTensorEvaluationSourceFieldIso k R M P).hom ≫
    ModuleCat.ofHom lP.toLinearMap) =
    ((envelopingRingDualTensorEvaluationSourceFieldIso k R M Q).hom ≫
      ModuleCat.ofHom lQ.toLinearMap) ≫ _
  rw [← Category.assoc, envelopingRingDualTensorEvaluationSourceFieldIso_naturality,
    Category.assoc, hn, ← Category.assoc]

noncomputable def envelopingFiniteProjectiveRingDualTensorComplexIso
    {ι : Type t} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{v} (AlgebraEnvelopingRing k R)) c)
    (hK : ∀ i, ordinaryFiniteProjectiveProperty (AlgebraEnvelopingRing k R) (K.X i)) :
    ((envelopingRingDualTensorEvaluationSourceFunctor k R M).mapHomologicalComplex c.symm).obj K.op ≅
      ((envelopingRingDualTensorEvaluationTargetFunctor k R M).mapHomologicalComplex c.symm).obj K.op :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => envelopingFiniteProjectiveRingDualTensorTermIso k R M (K.X i) (hK i))
    (fun i j _ => (envelopingFiniteProjectiveRingDualTensorTermIso_naturality
      k R M (hK j) (hK i) (K.d j i)).symm)

end ASGinzburg
