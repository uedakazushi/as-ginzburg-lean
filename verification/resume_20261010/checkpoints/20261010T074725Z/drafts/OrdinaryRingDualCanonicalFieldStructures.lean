import ASGinzburg.GradedOrdinaryRingDualComponents

/-! Canonical additive and field-module dictionaries on the actual
ordinary ring dual, read from its genuine unbundled linear-map carrier. -/
namespace ASGinzburg
open CategoryTheory
universe u v
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]

noncomputable abbrev ordinaryRingDualUnbundledAddCommGroup (P : ModuleCat.{v} R) :
    AddCommGroup (ordinaryRingDual R P) :=
  inferInstanceAs (AddCommGroup (P →ₗ[R] R))

noncomputable abbrev ordinaryRingDualUnbundledFieldModule (P : ModuleCat.{v} R) :
    Module k (ordinaryRingDual R P) :=
  inferInstanceAs (Module k (P →ₗ[R] R))

end ASGinzburg
