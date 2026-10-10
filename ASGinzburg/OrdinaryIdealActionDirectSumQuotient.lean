import ASGinzburg.OrdinaryIdealActionSubmodule

/-! The same ideal-action top decomposition is an actual ordinary
ring-linear quotient isomorphism, with the quotient actions inherited. -/
namespace ASGinzburg
open scoped DirectSum
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable {ι : Type z} [DecidableEq ι] (M : ι → Type w)
variable [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)] [∀ i, Module R (M i)]
variable [∀ i, IsScalarTower k R (M i)] (I : Ideal R)

noncomputable def ordinaryIdealActionDirectSumQuotientMap :
    (⨁ i, M i) →ₗ[R] ⨁ i, (M i ⧸ ordinaryIdealActionSubmodule k R (M i) I) :=
  DirectSum.lmap (fun i => (ordinaryIdealActionSubmodule k R (M i) I).mkQ)

omit [DecidableEq ι] in
@[simp] theorem ordinaryIdealActionDirectSumQuotientMap_apply (x : ⨁ i, M i) (i : ι) :
    ordinaryIdealActionDirectSumQuotientMap k R M I x i =
      (ordinaryIdealActionSubmodule k R (M i) I).mkQ (x i) := rfl

omit [DecidableEq ι] in
theorem ordinaryIdealActionDirectSumQuotientMap_surjective :
    Function.Surjective (ordinaryIdealActionDirectSumQuotientMap k R M I) :=
  (DirectSum.lmap_surjective _).mpr
    (fun i => (ordinaryIdealActionSubmodule k R (M i) I).mkQ_surjective)

theorem ordinaryIdealActionDirectSumQuotientMap_ker :
    LinearMap.ker (ordinaryIdealActionDirectSumQuotientMap k R M I) =
      ordinaryIdealActionSubmodule k R (⨁ i, M i) I := by
  ext x
  change ordinaryIdealActionDirectSumQuotientMap k R M I x = 0 ↔
    x ∈ ordinaryIdealActionSpan k R (⨁ i, M i) I
  rw [ordinaryIdealActionSpan_directSum_iff k R M I x]
  constructor
  · intro hx i
    have hi := congrArg (fun z => z i) hx
    change (ordinaryIdealActionSubmodule k R (M i) I).mkQ (x i) = 0 at hi
    exact (Submodule.Quotient.mk_eq_zero _).mp hi
  · intro hx
    apply DFinsupp.ext
    intro i
    change (ordinaryIdealActionSubmodule k R (M i) I).mkQ (x i) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr (hx i)

noncomputable def ordinaryIdealActionDirectSumQuotientEquiv :
    ((⨁ i, M i) ⧸ ordinaryIdealActionSubmodule k R (⨁ i, M i) I) ≃ₗ[R]
      ⨁ i, (M i ⧸ ordinaryIdealActionSubmodule k R (M i) I) :=
  (Submodule.quotEquivOfEq _ _
    (ordinaryIdealActionDirectSumQuotientMap_ker k R M I).symm).trans
    ((ordinaryIdealActionDirectSumQuotientMap k R M I).quotKerEquivOfSurjective
      (ordinaryIdealActionDirectSumQuotientMap_surjective k R M I))

@[simp] theorem ordinaryIdealActionDirectSumQuotientEquiv_mkQ (x : ⨁ i, M i) :
    ordinaryIdealActionDirectSumQuotientEquiv k R M I
      ((ordinaryIdealActionSubmodule k R (⨁ i, M i) I).mkQ x) =
      ordinaryIdealActionDirectSumQuotientMap k R M I x := rfl

end ASGinzburg
