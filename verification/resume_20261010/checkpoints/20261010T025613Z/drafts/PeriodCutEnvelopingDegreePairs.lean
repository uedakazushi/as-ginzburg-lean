import work.ASGinzburgDraft.PeriodCutEnvelopingDegreeDecomposition

/-! Every actual total-degree block of the ordinary enveloping algebra
contains exactly n+1 degree pairs. Degree zero is a single pair. -/
namespace ASGinzburg.ZAlgebra.PeriodIso

noncomputable def cutEnvelopingDegreePairFinEquiv (n : ℕ) :
    CutEnvelopingDegreePairs n ≃ Fin (n+1) where
  toFun d := ⟨d.val.1, by have hd := d.property; omega⟩
  invFun i := ⟨(i.val, n-i.val), by omega⟩
  left_inv d := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hd := d.property
      dsimp
      omega
  right_inv i := by
    apply Fin.ext
    rfl

noncomputable instance cutEnvelopingDegreePairFintype (n : ℕ) :
    Fintype (CutEnvelopingDegreePairs n) :=
  Fintype.ofEquiv (Fin (n+1)) (cutEnvelopingDegreePairFinEquiv n).symm

theorem cutEnvelopingDegreePair_card (n : ℕ) :
    Fintype.card (CutEnvelopingDegreePairs n)=n+1 := by
  rw [Fintype.card_congr (cutEnvelopingDegreePairFinEquiv n), Fintype.card_fin]

theorem cutEnvelopingDegreePair_zero (d : CutEnvelopingDegreePairs 0) : d.val=(0,0) := by
  have hd := d.property
  apply Prod.ext <;> dsimp <;> omega

end ASGinzburg.ZAlgebra.PeriodIso
