import work.ASGinzburgDraft.QuadraticResolutionComponents

/-! The actual AS resolution yields its componentwise Euler recurrence
with incoming/outgoing arrow sums and the tau-inverse top term. -/

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

/-- A finite coproduct is finite at a component whenever its actual summands are. -/
theorem rightFiniteCoproductComponentFinite {I : Type} [Fintype I] [DecidableEq I]
    (g : I → A.RightModule) (i : ℤ)
    [∀ a, Module.Finite k ((A.rightModuleEvaluation i).obj (g a))] :
    Module.Finite k ((A.rightModuleEvaluation i).obj (∐ g)) :=
  Module.Finite.of_injective (A.rightFiniteCoproductPiEquiv g i).toLinearMap
    (A.rightFiniteCoproductPiEquiv g i).injective

theorem rightFiniteCoproductComponent_finrank {I : Type} [Fintype I] [DecidableEq I]
    (g : I → A.RightModule) (i : ℤ)
    [∀ a, Module.Finite k ((A.rightModuleEvaluation i).obj (g a))] :
    Module.finrank k ((A.rightModuleEvaluation i).obj (∐ g)) =
      ∑ a, Module.finrank k ((A.rightModuleEvaluation i).obj (g a)) := by
  rw [(A.rightFiniteCoproductPiEquiv g i).finrank_eq, Module.finrank_pi_fintype]

variable (Q : CutQuiver)

theorem asResolutionTerm₁ComponentFinite (w : Q.LiftVertex) (i : ℤ) :
    Module.Finite k ((A.rightModuleEvaluation i).obj (A.asResolutionTerm₁ Q w)) := by
  classical
  dsimp only [asResolutionTerm₁]
  letI : ∀ a : Q.incomingArrows w, Module.Finite k
      ((A.rightModuleEvaluation i).obj (A.representable (Q.height (Q.incomingSource w a)))) :=
    fun a => A.finite i (Q.height (Q.incomingSource w a))
  exact A.rightFiniteCoproductComponentFinite _ i

theorem asResolutionTerm₂ComponentFinite (w : Q.LiftVertex) (i : ℤ) :
    Module.Finite k ((A.rightModuleEvaluation i).obj (A.asResolutionTerm₂ Q w)) := by
  classical
  dsimp only [asResolutionTerm₂]
  letI : ∀ a : Q.outgoingArrows (Q.tau.symm w), Module.Finite k
      ((A.rightModuleEvaluation i).obj
        (A.representable (Q.height (Q.outgoingTarget (Q.tau.symm w) a)))) :=
    fun a => A.finite i (Q.height (Q.outgoingTarget (Q.tau.symm w) a))
  exact A.rightFiniteCoproductComponentFinite _ i

theorem asResolutionTerm₁Component_finrank (w : Q.LiftVertex) (i : ℤ) :
    Module.finrank k ((A.rightModuleEvaluation i).obj (A.asResolutionTerm₁ Q w)) =
      ∑ a : Q.incomingArrows w, Module.finrank k (A.Hom i (Q.height (Q.incomingSource w a))) := by
  classical
  dsimp only [asResolutionTerm₁]
  letI : ∀ a : Q.incomingArrows w, Module.Finite k
      ((A.rightModuleEvaluation i).obj (A.representable (Q.height (Q.incomingSource w a)))) :=
    fun a => A.finite i (Q.height (Q.incomingSource w a))
  rw [A.rightFiniteCoproductComponent_finrank]
  rfl

theorem asResolutionTerm₂Component_finrank (w : Q.LiftVertex) (i : ℤ) :
    Module.finrank k ((A.rightModuleEvaluation i).obj (A.asResolutionTerm₂ Q w)) =
      ∑ a : Q.outgoingArrows (Q.tau.symm w),
        Module.finrank k (A.Hom i (Q.height (Q.outgoingTarget (Q.tau.symm w) a))) := by
  classical
  dsimp only [asResolutionTerm₂]
  letI : ∀ a : Q.outgoingArrows (Q.tau.symm w), Module.Finite k
      ((A.rightModuleEvaluation i).obj
        (A.representable (Q.height (Q.outgoingTarget (Q.tau.symm w) a)))) :=
    fun a => A.finite i (Q.height (Q.outgoingTarget (Q.tau.symm w) a))
  rw [A.rightFiniteCoproductComponent_finrank]
  rfl

/-- The actual unrolled component form of source (4.2). -/
theorem ASResolution.component_euler {A : ZAlgebra.{u,v} k} {Q : CutQuiver} {w : Q.LiftVertex}
    (R : A.ASResolution Q w) (i : ℤ) :
    (Module.finrank k (A.Hom i (Q.height w)) : ℤ) -
      (∑ a : Q.incomingArrows w, Module.finrank k (A.Hom i (Q.height (Q.incomingSource w a)))) +
      (∑ a : Q.outgoingArrows (Q.tau.symm w),
        Module.finrank k (A.Hom i (Q.height (Q.outgoingTarget (Q.tau.symm w) a)))) -
      Module.finrank k (A.Hom i (Q.height (Q.tau.symm w))) =
      if i = Q.height w then 1 else 0 := by
  classical
  let F := A.rightModuleEvaluation i
  haveI := A.asResolutionTerm₁ComponentFinite Q w i
  haveI := A.asResolutionTerm₂ComponentFinite Q w i
  haveI : Module.Finite k (F.obj (A.representable (Q.height w))) := A.finite i (Q.height w)
  haveI := R.mono_d₃
  have he := moduleCatFourTermEuler (F.map R.d₃) (F.map R.d₂) (F.map R.d₁)
    (F.map (A.simpleRightModuleπ (Q.height w)))
    (R.exact₂.map F).moduleCat_range_eq_ker
    (R.exact₁.map F).moduleCat_range_eq_ker
    (R.exact₀.map F).moduleCat_range_eq_ker
  change (Module.finrank k (A.Hom i (Q.height w)) : ℤ) -
    Module.finrank k ((A.rightModuleEvaluation i).obj (A.asResolutionTerm₁ Q w)) +
    Module.finrank k ((A.rightModuleEvaluation i).obj (A.asResolutionTerm₂ Q w)) -
    Module.finrank k (A.Hom i (Q.height (Q.tau.symm w))) =
    Module.finrank k ((A.rightModuleEvaluation i).obj (A.simpleRightModule (Q.height w))) at he
  rw [A.asResolutionTerm₁Component_finrank, A.asResolutionTerm₂Component_finrank,
    A.simpleRightModule_component_finrank] at he
  simpa only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using he

end ASGinzburg.ZAlgebra
