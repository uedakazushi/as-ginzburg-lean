import ASGinzburg.CoproductRadicals
import Mathlib.LinearAlgebra.Quotient.Pi

/-! The actual top of a finite coproduct is the product of its component tops. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)
variable {I : Type} [Fintype I] [DecidableEq I] (g : I → A.RightModule)

theorem rightFiniteCoproduct_radical_map (i : ℤ) :
    Submodule.map (A.rightFiniteCoproductPiEquiv g i).toLinearMap
      (A.positiveActionSpan (∐ g) i) =
      Submodule.pi Set.univ (fun a => A.positiveActionSpan (g a) i) := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact Submodule.mem_pi.mpr (fun a _ => (A.rightFiniteCoproduct_radical_iff g i y).mp hy a)
  · intro hx
    obtain ⟨y,rfl⟩ := (A.rightFiniteCoproductPiEquiv g i).surjective x
    refine ⟨y,?_,rfl⟩
    exact (A.rightFiniteCoproduct_radical_iff g i y).mpr
      (fun a => Submodule.mem_pi.mp hx a (Set.mem_univ a))

noncomputable def rightFiniteCoproductTopEquiv (i : ℤ) :
    ((A.rightModuleEvaluation i).obj (∐ g) ⧸ A.positiveActionSpan (∐ g) i) ≃ₗ[k]
      (∀ a, (A.rightModuleEvaluation i).obj (g a) ⧸ A.positiveActionSpan (g a) i) :=
  (Submodule.Quotient.equiv _ _ (A.rightFiniteCoproductPiEquiv g i)
    (A.rightFiniteCoproduct_radical_map g i)).trans
      (Submodule.quotientPi (fun a => A.positiveActionSpan (g a) i))

end ASGinzburg.ZAlgebra
