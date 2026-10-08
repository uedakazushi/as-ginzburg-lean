import ASGinzburg.LeftModuleProjectives

/-!
# Enough projectives for linear left modules

Each module is a quotient of the coproduct indexed by all its vertex elements.
This is an unrestricted projective presentation, not the finite minimal
four-term resolution required by the paper's AS condition.
-/

namespace ASGinzburg.ZAlgebra

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

/-- Index all elements in all vertex components; no finite generation is assumed. -/
abbrev leftModuleGenerators (M : A.LeftModule) :=
  Σ i : ℤ, (A.leftModuleEvaluation i).obj M

/-- A coproduct of actual representables providing enough projectives. -/
noncomputable def freeLeftModule (M : A.LeftModule) : A.LeftModule :=
  ∐ fun g : A.leftModuleGenerators M => A.leftRepresentable g.1

/-- Send each distinguished generator to the corresponding element of the target module. -/
noncomputable def freeLeftModuleπ (M : A.LeftModule) : A.freeLeftModule M ⟶ M :=
  Sigma.desc fun g => (A.leftRepresentableYonedaEquiv g.1 M).symm g.2

noncomputable instance freeLeftModuleProjective (M : A.LeftModule) :
    Projective (A.freeLeftModule M) := by
  dsimp [freeLeftModule]
  infer_instance

noncomputable instance freeLeftModuleπEpi (M : A.LeftModule) : Epi (A.freeLeftModuleπ M) := by
  apply (A.leftModule_epi_iff_surjective _).mpr
  intro i x
  let g : A.leftModuleGenerators M := ⟨i, x⟩
  refine ⟨(A.leftModuleEvaluation i).map
    (Sigma.ι (fun g : A.leftModuleGenerators M => A.leftRepresentable g.1) g) (A.id i), ?_⟩
  have h := Sigma.ι_desc (fun g : A.leftModuleGenerators M =>
    (A.leftRepresentableYonedaEquiv g.1 M).symm g.2) g
  have h' := congrArg (A.leftRepresentableYonedaEquiv i M) h
  rw [A.leftRepresentableYonedaEquiv_comp, LinearEquiv.apply_symm_apply] at h'
  exact h'

/-- The existing category has enough projectives, via explicit coproduct presentations. -/
noncomputable instance leftModuleEnoughProjectives : EnoughProjectives A.LeftModule where
  presentation M := ⟨{ p := A.freeLeftModule M, f := A.freeLeftModuleπ M }⟩

end ASGinzburg.ZAlgebra
