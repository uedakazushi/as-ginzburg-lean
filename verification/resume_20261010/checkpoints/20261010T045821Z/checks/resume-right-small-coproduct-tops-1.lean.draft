import work.ASGinzburgDraft.RightSmallCoproductRadicals
import Mathlib.LinearAlgebra.Isomorphisms

/-! The genuine top of an arbitrary small right-module coproduct is
canonically the direct sum of its actual radical quotient spaces. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)
variable {I : Type v} [DecidableEq I] (g : I → A.RightModule)

noncomputable def rightSmallCoproductTopMap (i : ℤ) :
    (A.rightModuleEvaluation i).obj (∐ g) →ₗ[k]
      ⨁ a, ((A.rightModuleEvaluation i).obj (g a) ⧸ A.positiveActionSpan (g a) i) :=
  (DirectSum.lmap (fun a => (A.positiveActionSpan (g a) i).mkQ)).comp
    (A.rightSmallCoproductComponentIso g i).hom.hom

theorem rightSmallCoproductTopMap_surjective (i : ℤ) :
    Function.Surjective (A.rightSmallCoproductTopMap g i) :=
  ((DirectSum.lmap_surjective _).mpr (fun a => (A.positiveActionSpan (g a) i).mkQ_surjective)).comp
    (A.rightSmallCoproductComponentIso g i).toLinearEquiv.surjective

theorem rightSmallCoproductTopMap_ker (i : ℤ) :
    LinearMap.ker (A.rightSmallCoproductTopMap g i) = A.positiveActionSpan (∐ g) i := by
  ext x
  rw [A.rightSmallCoproduct_radical_iff g i x]
  constructor
  · intro hx a
    have ha := congrArg (fun z => z a) hx
    change (A.positiveActionSpan (g a) i).mkQ
      ((A.rightSmallCoproductComponentIso g i).hom.hom x a) = 0 at ha
    exact (Submodule.Quotient.mk_eq_zero _).mp ha
  · intro hx
    apply DFinsupp.ext
    intro a
    change (A.positiveActionSpan (g a) i).mkQ
      ((A.rightSmallCoproductComponentIso g i).hom.hom x a) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr (hx a)

noncomputable def rightSmallCoproductTopEquiv (i : ℤ) :
    ((A.rightModuleEvaluation i).obj (∐ g) ⧸ A.positiveActionSpan (∐ g) i) ≃ₗ[k]
      ⨁ a, ((A.rightModuleEvaluation i).obj (g a) ⧸ A.positiveActionSpan (g a) i) :=
  (Submodule.quotEquivOfEq _ _ (A.rightSmallCoproductTopMap_ker g i).symm).trans
    ((A.rightSmallCoproductTopMap g i).quotKerEquivOfSurjective
      (A.rightSmallCoproductTopMap_surjective g i))

end ASGinzburg.ZAlgebra
