import work.ASGinzburgDraft.GradedOrdinaryRingDualTopQuotientFinite

/-! A bundled name for the genuine field-linear ordinary ring-dual
cokernel, retaining its canonical field structure when native carriers
also carry other field structures. -/
namespace ASGinzburg
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]

noncomputable def ordinaryRingDualTopQuotient {L M : ModuleCat.{v} R} (a : M ⟶ L) : Type v :=
  ordinaryRingDual R M ⧸ LinearMap.range (ordinaryRingDualMapField (k := k) a)

noncomputable instance ordinaryRingDualTopQuotientAddCommGroup {L M : ModuleCat.{v} R}
    (a : M ⟶ L) : AddCommGroup (ordinaryRingDualTopQuotient k R a) := by
  unfold ordinaryRingDualTopQuotient
  infer_instance

noncomputable instance ordinaryRingDualTopQuotientModule {L M : ModuleCat.{v} R}
    (a : M ⟶ L) : Module k (ordinaryRingDualTopQuotient k R a) := by
  unfold ordinaryRingDualTopQuotient
  infer_instance

end ASGinzburg
