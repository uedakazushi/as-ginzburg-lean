import ASGinzburg.RightModuleProjectives

/-!
# Enough projectives for linear right modules

Each module is a quotient of the coproduct indexed by all its vertex elements.
This is an unrestricted projective presentation, not the finite minimal
four-term resolution required by the paper's AS condition.
-/

namespace ASGinzburg.ZAlgebra

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

/-- Index all elements in all vertex components; no finite generation is assumed. -/
abbrev rightModuleGenerators (M : A.RightModule) :=
  Σ i : ℤ, (A.rightModuleEvaluation i).obj M

/-- A coproduct of actual representables providing enough projectives. -/
noncomputable def freeRightModule (M : A.RightModule) : A.RightModule :=
  ∐ fun g : A.rightModuleGenerators M => A.representable g.1

/-- Send each distinguished generator to the corresponding element of the target module. -/
noncomputable def freeRightModuleπ (M : A.RightModule) : A.freeRightModule M ⟶ M :=
  Sigma.desc fun g => (A.representableYonedaEquiv g.1 M).symm g.2

noncomputable instance freeRightModuleProjective (M : A.RightModule) :
    Projective (A.freeRightModule M) := by
  dsimp [freeRightModule]
  infer_instance

noncomputable instance freeRightModuleπEpi (M : A.RightModule) : Epi (A.freeRightModuleπ M) := by
  apply (A.rightModule_epi_iff_surjective _).mpr
  intro i x
  let g : A.rightModuleGenerators M := ⟨i, x⟩
  refine ⟨(A.rightModuleEvaluation i).map
    (Sigma.ι (fun g : A.rightModuleGenerators M => A.representable g.1) g) (A.id i), ?_⟩
  have h := Sigma.ι_desc (fun g : A.rightModuleGenerators M =>
    (A.representableYonedaEquiv g.1 M).symm g.2) g
  have h' := congrArg (A.representableYonedaEquiv i M) h
  rw [A.representableYonedaEquiv_comp, LinearEquiv.apply_symm_apply] at h'
  exact h'

/-- The existing category has enough projectives, via explicit coproduct presentations. -/
noncomputable instance rightModuleEnoughProjectives : EnoughProjectives A.RightModule where
  presentation M := ⟨{ p := A.freeRightModule M, f := A.freeRightModuleπ M }⟩

end ASGinzburg.ZAlgebra
