import ASGinzburg.OrdinaryIdealActionDirectSum

/-! The actual ideal action span is stable under the ordinary ring action.
Its ordinary submodule and ordinary quotient require no extra module data. -/
namespace ASGinzburg
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module R M]
variable [IsScalarTower k R M] (I : Ideal R)

theorem ordinaryIdealActionSpan_smul_mem (r : R) {x : M}
    (hx : x ∈ ordinaryIdealActionSpan k R M I) :
    r • x ∈ ordinaryIdealActionSpan k R M I := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨s, hs, x, rfl⟩ := hy
    exact Submodule.subset_span ⟨r * s, I.mul_mem_left r hs, x, mul_smul r s x⟩
  | zero => simpa only [smul_zero] using (ordinaryIdealActionSpan k R M I).zero_mem
  | add x y hx hy ihx ihy =>
    simpa only [smul_add] using (ordinaryIdealActionSpan k R M I).add_mem ihx ihy
  | smul c x hx ihx =>
    rw [← smul_comm c r x]
    exact (ordinaryIdealActionSpan k R M I).smul_mem c ihx

def ordinaryIdealActionSubmodule : Submodule R M where
  carrier := ordinaryIdealActionSpan k R M I
  zero_mem' := (ordinaryIdealActionSpan k R M I).zero_mem
  add_mem' := (ordinaryIdealActionSpan k R M I).add_mem
  smul_mem' := fun r _ hx => ordinaryIdealActionSpan_smul_mem k R M I r hx

@[simp] theorem ordinaryIdealActionSubmodule_mem (x : M) :
    x ∈ ordinaryIdealActionSubmodule k R M I ↔ x ∈ ordinaryIdealActionSpan k R M I :=
  Iff.rfl

theorem ordinaryIdealActionSubmodule_restrictScalars :
    (ordinaryIdealActionSubmodule k R M I).restrictScalars k =
      ordinaryIdealActionSpan k R M I := by
  ext x
  rfl

noncomputable def ordinaryIdealActionTopRestrictScalarsEquiv :
    (M ⧸ ordinaryIdealActionSpan k R M I) ≃ₗ[k]
      (M ⧸ ordinaryIdealActionSubmodule k R M I) :=
  (Submodule.quotEquivOfEq _ _
    (ordinaryIdealActionSubmodule_restrictScalars k R M I).symm).trans
    (Submodule.Quotient.restrictScalarsEquiv k
      (ordinaryIdealActionSubmodule k R M I))

@[simp] theorem ordinaryIdealActionTopRestrictScalarsEquiv_mkQ (x : M) :
    ordinaryIdealActionTopRestrictScalarsEquiv k R M I
      ((ordinaryIdealActionSpan k R M I).mkQ x) =
      (ordinaryIdealActionSubmodule k R M I).mkQ x := rfl

theorem ordinaryIdealActionSubmodule_map_mem
    {N : Type z} [AddCommGroup N] [Module k N] [Module R N]
    [IsScalarTower k R N]
    (f : M →ₗ[R] N) {x : M}
    (hx : x ∈ ordinaryIdealActionSubmodule k R M I) :
    f x ∈ ordinaryIdealActionSubmodule k R N I :=
  ordinaryIdealActionSpan_map_mem k R I f hx

noncomputable def ordinaryIdealActionTopMap
    {N : Type z} [AddCommGroup N] [Module k N] [Module R N]
    [IsScalarTower k R N] (f : M →ₗ[R] N) :
    (M ⧸ ordinaryIdealActionSubmodule k R M I) →ₗ[R]
      (N ⧸ ordinaryIdealActionSubmodule k R N I) :=
  (ordinaryIdealActionSubmodule k R M I).mapQ
    (ordinaryIdealActionSubmodule k R N I) f
    (fun _ hx => ordinaryIdealActionSubmodule_map_mem k R M I f hx)

@[simp] theorem ordinaryIdealActionTopMap_mkQ
    {N : Type z} [AddCommGroup N] [Module k N] [Module R N]
    [IsScalarTower k R N] (f : M →ₗ[R] N) (x : M) :
    ordinaryIdealActionTopMap k R M I f
      ((ordinaryIdealActionSubmodule k R M I).mkQ x) =
      (ordinaryIdealActionSubmodule k R N I).mkQ (f x) := rfl

end ASGinzburg
