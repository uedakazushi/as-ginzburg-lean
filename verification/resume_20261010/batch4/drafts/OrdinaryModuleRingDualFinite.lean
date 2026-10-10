import work.ASGinzburgDraft.OrdinaryModuleRingDual
import ASGinzburg.OrdinaryModuleFiniteFreeRetract

/-! The actual contravariant ring dual preserves finite projective
ordinary modules by transporting their genuine finite free retracts. -/
namespace ASGinzburg
open CategoryTheory
universe v
variable (R : Type v) [Ring R]

theorem ordinaryFiniteProjectiveProperty_ringDual {P : ModuleCat.{v} R}
    (hP : ordinaryFiniteProjectiveProperty R P) :
    ordinaryFiniteProjectiveProperty Rᵐᵒᵖ (ordinaryRingDual R P) := by
  obtain ⟨n, ⟨r⟩⟩ := hP
  exact ⟨n, ⟨(r.op.map (ordinaryRingDualFunctor R)).trans
    (Retract.ofIso (ordinaryRingDualFiniteFreeEquiv R n).toModuleIso)⟩⟩

theorem ordinaryRingDualHom_finite (P : ModuleCat.{v} R)
    [Module.Finite R P] [Projective P] :
    Module.Finite Rᵐᵒᵖ (P →ₗ[R] R) :=
  ((ordinaryFiniteProjectiveProperty_iff Rᵐᵒᵖ (ordinaryRingDual R P)).mp
    (ordinaryFiniteProjectiveProperty_ringDual R
      (ordinaryModule_finiteFreeRetract R P))).1

theorem ordinaryRingDual_projective (P : ModuleCat.{v} R)
    [Module.Finite R P] [Projective P] : Projective (ordinaryRingDual R P) :=
  ((ordinaryFiniteProjectiveProperty_iff Rᵐᵒᵖ (ordinaryRingDual R P)).mp
    (ordinaryFiniteProjectiveProperty_ringDual R
      (ordinaryModule_finiteFreeRetract R P))).2

theorem ordinaryRingDualHom_projective (P : ModuleCat.{v} R)
    [Module.Finite R P] [Projective P] : Module.Projective Rᵐᵒᵖ (P →ₗ[R] R) := by
  letI := ordinaryRingDual_projective R P
  exact ModuleCat.projective_of_module_projective (ordinaryRingDual R P)

end ASGinzburg
