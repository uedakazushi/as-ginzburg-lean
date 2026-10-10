import ASGinzburg.PeriodCutGradedModuleEnrichment

/-! The actual graded Hom groups and their field action, read from
the genuine field-linear graded Hom submodule. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices : ℤ))

noncomputable abbrev cutOrdinaryRingDualTopHomAddCommGroup
    (M N : E.CutGradedRightModule Q) : AddCommGroup (M ⟶ N) :=
  inferInstanceAs (AddCommGroup ↥(CutGradedRightModule.homSubmodule M N))

noncomputable abbrev cutOrdinaryRingDualTopHomFieldModule
    (M N : E.CutGradedRightModule Q) : Module k (M ⟶ N) :=
  inferInstanceAs (Module k ↥(CutGradedRightModule.homSubmodule M N))

end ASGinzburg.ZAlgebra.PeriodIso
