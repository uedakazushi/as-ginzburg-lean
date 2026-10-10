import work.ASGinzburgDraft.OrdinaryModuleRingDualDerived
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! The genuine contravariant ring dual preserves limits. Its underlying
set-valued functor is represented by the regular left module, and the
module forgetful functor reflects limits. Consequently the actual zeroth
right derived functor is canonically the ring dual. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits Opposite
universe v
variable (R : Type v) [Ring R]

noncomputable def ordinaryRingDualForgetYonedaIso :
    ordinaryRingDualFunctor R ⋙ forget (ModuleCat.{v} Rᵐᵒᵖ) ≅
      yoneda.obj (ModuleCat.of R R) :=
  NatIso.ofComponents
    (fun P => ({
      toFun := ModuleCat.ofHom
      invFun := fun f => f.hom
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } :
        ordinaryRingDual R P.unop ≃ (P.unop ⟶ ModuleCat.of R R)).toIso)
    (fun f => by funext g; rfl)

instance ordinaryRingDualFunctor_preservesLimits : PreservesLimits (ordinaryRingDualFunctor R) := by
  letI : PreservesLimits
      (ordinaryRingDualFunctor R ⋙ forget (ModuleCat.{v} Rᵐᵒᵖ)) :=
    preservesLimits_of_natIso (ordinaryRingDualForgetYonedaIso R).symm
  exact preservesLimits_of_reflects_of_preserves
    (ordinaryRingDualFunctor R) (forget (ModuleCat.{v} Rᵐᵒᵖ))

instance ordinaryRingDualFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (ordinaryRingDualFunctor R) := inferInstance

instance ordinaryRingDualFunctor_preservesMonomorphisms :
    (ordinaryRingDualFunctor R).PreservesMonomorphisms := inferInstance

theorem ordinaryRingDual_map_exact_of_mono
    (S : ShortComplex (ModuleCat.{v} R)ᵒᵖ) (hS : S.Exact) [Mono S.f] :
    (S.map (ordinaryRingDualFunctor R)).Exact :=
  hS.map_of_mono_of_preservesKernel (ordinaryRingDualFunctor R) inferInstance inferInstance

theorem ordinaryRingDual_shortExact_leftExact
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact) :
    (S.op.map (ordinaryRingDualFunctor R)).Exact ∧
      Mono (S.op.map (ordinaryRingDualFunctor R)).f := by
  letI : Mono S.op.f := hS.op.mono_f
  refine ⟨ordinaryRingDual_map_exact_of_mono R S.op hS.exact.op, ?_⟩
  exact inferInstanceAs (Mono ((ordinaryRingDualFunctor R).map S.op.f))

theorem ordinaryRingDual_preservesLeftHomology_of_zero_f
    (S : ShortComplex (ModuleCat.{v} R)ᵒᵖ) (hf : S.f = 0) :
    (ordinaryRingDualFunctor R).PreservesLeftHomologyOf S :=
  (ordinaryRingDualFunctor R).preservesLeftHomology_of_zero_f S hf

noncomputable def ordinaryRingDualExtZeroIso :
    ordinaryRingDualExtFunctor R 0 ≅ ordinaryRingDualFunctor R :=
  (ordinaryRingDualFunctor R).rightDerivedZeroIsoSelf

noncomputable def ordinaryRingDualExtZeroObjIso (P : ModuleCat.{v} R) :
    (ordinaryRingDualExtFunctor R 0).obj (op P) ≅ ordinaryRingDual R P :=
  (ordinaryRingDualExtZeroIso R).app (op P)

@[simp] theorem ordinaryRingDualExtZeroIso_inv :
    (ordinaryRingDualExtZeroIso R).inv =
      (ordinaryRingDualFunctor R).toRightDerivedZero := rfl

@[reassoc (attr := simp)]
theorem ordinaryRingDualExtZeroIso_hom_toRightDerivedZero :
    (ordinaryRingDualExtZeroIso R).hom ≫
        (ordinaryRingDualFunctor R).toRightDerivedZero = 𝟙 _ :=
  (ordinaryRingDualFunctor R).rightDerivedZeroIsoSelf_hom_inv_id

@[reassoc (attr := simp)]
theorem ordinaryRingDualExtZeroIso_toRightDerivedZero_hom :
    (ordinaryRingDualFunctor R).toRightDerivedZero ≫
        (ordinaryRingDualExtZeroIso R).hom = 𝟙 _ :=
  (ordinaryRingDualFunctor R).rightDerivedZeroIsoSelf_inv_hom_id

end ASGinzburg
