import ASGinzburg.LinearDirectSumHomogeneousDecomposition

/-! A map killing every positive degree has its genuine kernel generated
by the zero-degree kernel and the positive homogeneous subspaces. -/
namespace ASGinzburg
open scoped DirectSum
universe u v w z
variable (k : Type u) [Field k] (M : Type v) [AddCommMonoid M] [Module k M]
variable (B : ℕ → Type w) [∀ n, AddCommMonoid (B n)] [∀ n, Module k (B n)]
variable (e : M ≃ₗ[k] ⨁ n, B n)

noncomputable def linearDirectSumPositiveSubspace : Submodule k M :=
  ⨆ n : {n : ℕ // 0 < n}, linearDirectSumHomogeneousSubspace k M B e n.val

theorem linearDirectSumEraseZero_mem_positiveSubspace (y : ⨁ n, B n) :
    e.symm (y.erase 0) ∈ linearDirectSumPositiveSubspace k M B e := by
  induction y using DirectSum.induction_on with
  | zero =>
      change e.symm ((0 : ⨁ n, B n).erase 0) ∈ _
      simp only [DFinsupp.erase_zero, map_zero]
      exact Submodule.zero_mem _
  | of n b =>
      change e.symm ((DFinsupp.single n b).erase 0) ∈ _
      by_cases hn : n = 0
      · subst n
        rw [DFinsupp.erase_single_same]
        exact (e.symm.toLinearMap.map_zero) ▸ Submodule.zero_mem _
      · rw [DFinsupp.erase_single_ne b hn]
        exact (le_iSup
          (fun n : {n : ℕ // 0 < n} =>
            linearDirectSumHomogeneousSubspace k M B e n.val)
          ⟨n,Nat.pos_of_ne_zero hn⟩)
          (LinearMap.mem_range_self (linearDirectSumHomogeneousInclusion k M B e n) b)
  | add x y hx hy =>
      rw [DFinsupp.erase_add, e.symm.map_add]
      exact Submodule.add_mem _ hx hy

variable {N : Type z} [AddCommMonoid N] [Module k N] (f : M →ₗ[k] N)
variable (hpos : ∀ n : ℕ, 0 < n → ∀ b : B n,
  f (linearDirectSumHomogeneousInclusion k M B e n b) = 0)

include hpos

theorem linearDirectSumAugmentation_eq_zeroComponent (y : ⨁ n, B n) :
    f (e.symm y) = f (linearDirectSumHomogeneousInclusion k M B e 0 (y 0)) := by
  let g := f.comp e.symm.toLinearMap
  let h := (f.comp (linearDirectSumHomogeneousInclusion k M B e 0)).comp
    (DirectSum.component k ℕ B 0)
  change g y = h y
  induction y using DirectSum.induction_on with
  | zero => exact g.map_zero.trans h.map_zero.symm
  | of n b =>
      change f (linearDirectSumHomogeneousInclusion k M B e n b) =
        f (linearDirectSumHomogeneousInclusion k M B e 0 (DirectSum.of B n b 0))
      by_cases hn : n = 0
      · subst n
        rw [DirectSum.of_eq_same]
      · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hn),
          (linearDirectSumHomogeneousInclusion k M B e 0).map_zero, f.map_zero]
        exact hpos n (Nat.pos_of_ne_zero hn) b
  | add x y hx hy =>
      exact (g.map_add x y).trans
        ((congrArg₂ (· + ·) hx hy).trans (h.map_add x y).symm)

theorem linearDirectSumAugmentationKernel_eq_zero_sup_positive :
    LinearMap.ker f =
      (LinearMap.ker (f.comp (linearDirectSumHomogeneousInclusion k M B e 0))).map
        (linearDirectSumHomogeneousInclusion k M B e 0) ⊔
      linearDirectSumPositiveSubspace k M B e := by
  apply le_antisymm
  · intro x hx
    have hx0 : (e x) 0 ∈
        LinearMap.ker (f.comp (linearDirectSumHomogeneousInclusion k M B e 0)) := by
      change f (linearDirectSumHomogeneousInclusion k M B e 0 (e x 0)) = 0
      rw [← linearDirectSumAugmentation_eq_zeroComponent k M B e f hpos (e x),
        e.symm_apply_apply]
      exact hx
    have h0 : linearDirectSumHomogeneousInclusion k M B e 0 (e x 0) ∈
        (LinearMap.ker (f.comp (linearDirectSumHomogeneousInclusion k M B e 0))).map
          (linearDirectSumHomogeneousInclusion k M B e 0) :=
      Submodule.mem_map.mpr ⟨_,hx0,rfl⟩
    have hs := (Submodule.add_mem
      ( (LinearMap.ker (f.comp (linearDirectSumHomogeneousInclusion k M B e 0))).map
          (linearDirectSumHomogeneousInclusion k M B e 0) ⊔
        linearDirectSumPositiveSubspace k M B e)
      (Submodule.mem_sup_left h0)
      (Submodule.mem_sup_right
        (linearDirectSumEraseZero_mem_positiveSubspace k M B e (e x))))
    have heq : linearDirectSumHomogeneousInclusion k M B e 0 (e x 0) +
        e.symm ((e x).erase 0) = x := by
      change e.symm (DFinsupp.single 0 (e x 0)) + e.symm ((e x).erase 0) = x
      rw [← e.symm.map_add, DFinsupp.single_add_erase, e.symm_apply_apply]
    exact heq ▸ hs
  · apply sup_le
    · rintro x ⟨b,hb,rfl⟩
      exact hb
    · refine iSup_le fun n => ?_
      rintro x ⟨b,rfl⟩
      exact hpos n.val n.property b

end ASGinzburg
