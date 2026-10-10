import Mathlib.Algebra.DirectSum.Decomposition

/-! Extend a natural-indexed internal vector-space decomposition by zero in
negative integer degrees. -/

namespace ASGinzburg

universe u v

variable (k : Type u) (M : Type v) [Field k] [AddCommGroup M] [Module k M]
variable (G : ℕ → Submodule k M)

/-- The integer-indexed extension of natural homogeneous subspaces. -/
def natHomogeneousSubspaceIntegerExtension (q : ℤ) : Submodule k M :=
  if 0 ≤ q then G q.toNat else ⊥

@[simp]
theorem natHomogeneousSubspaceIntegerExtension_natCast (n : ℕ) :
    natHomogeneousSubspaceIntegerExtension k M G (n : ℤ) = G n := by
  simp [natHomogeneousSubspaceIntegerExtension]

theorem natHomogeneousSubspaceIntegerExtension_nonneg (q : ℤ) (hq : 0 ≤ q) :
    natHomogeneousSubspaceIntegerExtension k M G q = G q.toNat := by
  simp [natHomogeneousSubspaceIntegerExtension, hq]

theorem natHomogeneousSubspaceIntegerExtension_neg (q : ℤ) (hq : q < 0) :
    natHomogeneousSubspaceIntegerExtension k M G q = ⊥ := by
  simp [natHomogeneousSubspaceIntegerExtension, not_le_of_gt hq]

/-- Extending the indexing by zero preserves independence of the subspaces. -/
theorem natHomogeneousSubspaceIntegerExtension_iSupIndep (h : DirectSum.IsInternal G) :
    iSupIndep (natHomogeneousSubspaceIntegerExtension k M G) := by
  apply iSupIndep_ne_bot.mp
  let H := natHomogeneousSubspaceIntegerExtension k M G
  let f : {q : ℤ // H q ≠ ⊥} → ℕ := fun q ↦ q.1.toNat
  have hnonneg (q : {q : ℤ // H q ≠ ⊥}) : 0 ≤ q.1 := by
    by_contra hq
    exact q.2 (by simp [H, natHomogeneousSubspaceIntegerExtension, hq])
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have hab' : a.1.toNat = b.1.toNat := hab
    calc
      a.1 = (a.1.toNat : ℤ) := (Int.toNat_of_nonneg (hnonneg a)).symm
      _ = (b.1.toNat : ℤ) := congrArg (fun n : ℕ ↦ (n : ℤ)) hab'
      _ = b.1 := Int.toNat_of_nonneg (hnonneg b)
  have heq : (fun q : {q : ℤ // H q ≠ ⊥} ↦ H q) = G ∘ f := by
    funext q
    exact natHomogeneousSubspaceIntegerExtension_nonneg k M G q.1 (hnonneg q)
  change iSupIndep (fun q : {q : ℤ // H q ≠ ⊥} ↦ H q)
  rw [heq]
  exact h.submodule_iSupIndep.comp hf

/-- The extended subspaces still span the full vector space. -/
theorem natHomogeneousSubspaceIntegerExtension_iSup_eq_top (h : DirectSum.IsInternal G) :
    iSup (natHomogeneousSubspaceIntegerExtension k M G) = ⊤ := by
  apply top_unique
  calc
    ⊤ = iSup G := h.submodule_iSup_eq_top.symm
    _ ≤ iSup (natHomogeneousSubspaceIntegerExtension k M G) := by
      refine iSup_le fun n ↦ ?_
      rw [← natHomogeneousSubspaceIntegerExtension_natCast k M G n]
      exact le_iSup (natHomogeneousSubspaceIntegerExtension k M G) (n : ℤ)

/-- The zero extension gives an internal integer-indexed direct sum. -/
theorem natHomogeneousSubspaceIntegerExtension_isInternal (h : DirectSum.IsInternal G) :
    DirectSum.IsInternal (natHomogeneousSubspaceIntegerExtension k M G) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (natHomogeneousSubspaceIntegerExtension_iSupIndep k M G h)
    (natHomogeneousSubspaceIntegerExtension_iSup_eq_top k M G h)

/-- An explicit decomposition chosen from the extended internal direct sum. -/
noncomputable def natHomogeneousSubspaceIntegerExtensionDecomposition
    (h : DirectSum.IsInternal G) :
    DirectSum.Decomposition (natHomogeneousSubspaceIntegerExtension k M G) :=
  (natHomogeneousSubspaceIntegerExtension_isInternal k M G h).chooseDecomposition

end ASGinzburg
