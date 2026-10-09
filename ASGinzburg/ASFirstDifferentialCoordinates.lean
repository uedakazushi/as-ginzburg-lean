import ASGinzburg.ASLastArrowEvaluation
import ASGinzburg.FiniteRepresentableDualMatrix

/-! Actual AS d₁ in finite coproduct coordinates; this supplies the
commuting square from last-arrow path coordinates to the actual kernel. -/
namespace ASGinzburg.ZAlgebra.ASResolution
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k} {Q : CutQuiver}
  {w : Q.LiftVertex} (R : A.ASResolution Q w)

theorem d₁_component_pi_symm (i : ℤ)
    (x : ∀ a : Q.incomingArrows w, A.Hom i (Q.height (Q.incomingSource w a))) :
    ((A.rightModuleEvaluation i).map R.d₁).hom
      ((A.rightFiniteCoproductPiEquiv
        (fun a : Q.incomingArrows w => A.representable (Q.height (Q.incomingSource w a))) i).symm x)=
      ∑ a, A.comp (R.incomingElement a) (x a) := by
  classical
  have h := A.rightFiniteCoproductMorphism_apply
    (fun a : Q.incomingArrows w => A.representable (Q.height (Q.incomingSource w a)))
    (A.representable (Q.height w)) R.d₁ i
    ((A.rightFiniteCoproductPiEquiv
      (fun a : Q.incomingArrows w => A.representable (Q.height (Q.incomingSource w a))) i).symm x)
  simp only [LinearEquiv.apply_symm_apply] at h
  exact h.trans (Finset.sum_congr rfl (fun a _ => R.incomingElement_component a i (x a)))

end ASGinzburg.ZAlgebra.ASResolution
