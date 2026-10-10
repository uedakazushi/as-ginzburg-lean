import work.ASGinzburgDraft.OrdinaryIdealActionDirectSum

/-! A genuine module action sends scalar spans to action spans. Thus an
actual operator-span presentation of an ideal gives the same actual
ideal-action subspace on every module. -/
namespace ASGinzburg
universe u v w
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module R M]
  [IsScalarTower k R M]

def ordinaryOperatorActionSpan (S : Set R) : Submodule k M :=
  Submodule.span k {y : M | ∃ r ∈ S, ∃ x : M, r • x = y}

theorem ordinaryOperatorActionSpan_smul_mem_of_scalar_span (S : Set R)
    {r : R} (hr : r ∈ Submodule.span k S) (x : M) :
    r • x ∈ ordinaryOperatorActionSpan k R M S := by
  induction hr using Submodule.span_induction with
  | mem r hr => exact Submodule.subset_span ⟨r,hr,x,rfl⟩
  | zero => rw [zero_smul]; exact Submodule.zero_mem _
  | add r s hr hs ihr ihs => rw [add_smul]; exact Submodule.add_mem _ ihr ihs
  | smul c r hr ihr => rw [smul_assoc]; exact Submodule.smul_mem _ c ihr

theorem ordinaryIdealActionSpan_eq_operatorActionSpan (I : Ideal R) (S : Set R)
    (hI : ∀ r : R, r ∈ I ↔ r ∈ Submodule.span k S) :
    ordinaryIdealActionSpan k R M I = ordinaryOperatorActionSpan k R M S := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro y ⟨r,hr,x,rfl⟩
    exact ordinaryOperatorActionSpan_smul_mem_of_scalar_span k R M S ((hI r).mp hr) x
  · apply Submodule.span_le.mpr
    rintro y ⟨r,hr,x,rfl⟩
    exact Submodule.subset_span ⟨r,(hI r).mpr (Submodule.subset_span hr),x,rfl⟩

end ASGinzburg
