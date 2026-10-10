import ASGinzburg.ASResolutionComponentEuler
import ASGinzburg.ASComponentLowerTerms
import ASGinzburg.QuadraticHilbertGrowth

/-! The actual finite AS sequences determine all component dimensions.
The proof uses the exact Euler identity and strict index decreases,
without assuming periodicity or a numerical recurrence. -/

namespace ASGinzburg.ZAlgebra
universe u v v'
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

/-- Any two algebras admitting the original finite AS sequences for the
same cut quiver have the same actual component dimensions. -/
theorem component_finrank_eq_of_ASResolutions (B : ZAlgebra.{u,v'} k) (Q : CutQuiver)
    (hA : ∀ x : Q.LiftVertex, Nonempty (A.ASResolution Q x))
    (hB : ∀ x : Q.LiftVertex, Nonempty (B.ASResolution Q x)) (i j : ℤ) :
    Module.finrank k (A.Hom i j) = Module.finrank k (B.Hom i j) := by
  classical
  let dA : ℤ → ℤ → ℕ := fun s t => Module.finrank k (A.Hom s t)
  let dB : ℤ → ℤ → ℕ := fun s t => Module.finrank k (B.Hom s t)
  have hzero (s t : ℤ) (hts : t < s) : dA s t = dB s t :=
    (A.hom_finrank_eq_zero_of_lt s t hts).trans (B.hom_finrank_eq_zero_of_lt s t hts).symm
  have hmain : ∀ n : ℕ, ∀ s : ℤ, ∀ x : Q.LiftVertex, Q.height x - s = (n : ℤ) →
      dA s (Q.height x) = dB s (Q.height x) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s x hn
      have hlower (y : Q.LiftVertex) (hyx : Q.height y < Q.height x) :
          dA s (Q.height y) = dB s (Q.height y) := by
        by_cases hys : Q.height y < s
        · exact hzero s (Q.height y) hys
        · have hnonneg : 0 ≤ Q.height y - s := by omega
          have hsmall : (Q.height y - s).toNat < n := by omega
          exact ih _ hsmall s y (Int.toNat_of_nonneg hnonneg).symm
      have eA := (Classical.choice (hA x)).component_euler s
      have eB := (Classical.choice (hB x)).component_euler s
      change (dA s (Q.height x) : ℤ) -
        (∑ a : Q.incomingArrows x, dA s (Q.height (Q.incomingSource x a))) +
        (∑ a : Q.outgoingArrows (Q.tau.symm x),
          dA s (Q.height (Q.outgoingTarget (Q.tau.symm x) a))) -
        dA s (Q.height (Q.tau.symm x)) = if s = Q.height x then 1 else 0 at eA
      change (dB s (Q.height x) : ℤ) -
        (∑ a : Q.incomingArrows x, dB s (Q.height (Q.incomingSource x a))) +
        (∑ a : Q.outgoingArrows (Q.tau.symm x),
          dB s (Q.height (Q.outgoingTarget (Q.tau.symm x) a))) -
        dB s (Q.height (Q.tau.symm x)) = if s = Q.height x then 1 else 0 at eB
      have hs₁ : (∑ a : Q.incomingArrows x, dA s (Q.height (Q.incomingSource x a))) =
          ∑ a : Q.incomingArrows x, dB s (Q.height (Q.incomingSource x a)) := by
        apply Finset.sum_congr rfl
        intro a _
        exact hlower (Q.incomingSource x a) (Q.incomingSource_height_lt x a)
      have hs₂ : (∑ a : Q.outgoingArrows (Q.tau.symm x),
          dA s (Q.height (Q.outgoingTarget (Q.tau.symm x) a))) =
          ∑ a : Q.outgoingArrows (Q.tau.symm x),
            dB s (Q.height (Q.outgoingTarget (Q.tau.symm x) a)) := by
        apply Finset.sum_congr rfl
        intro a _
        exact hlower (Q.outgoingTarget (Q.tau.symm x) a) (Q.asSecondSource_height_lt x a)
      have ht := hlower (Q.tau.symm x) (Q.asTopSource_height_lt x)
      rw [hs₁, hs₂, ht] at eA
      omega
  change dA i j = dB i j
  by_cases hji : j < i
  · exact hzero i j hji
  · let x := Q.heightEquiv.symm j
    have hx : Q.height x = j := by
      dsimp only [x]
      rw [← Q.heightEquiv_apply, Equiv.apply_symm_apply]
    have hnonneg : 0 ≤ j - i := by omega
    have hd : Q.height x - i = ((j - i).toNat : ℤ) := by
      rw [hx]
      exact (Int.toNat_of_nonneg hnonneg).symm
    rw [← hx]
    exact hmain (j - i).toNat i x hd

theorem ASRegular.component_finrank_eq {B : ZAlgebra.{u,v'} k} {Q : CutQuiver}
    (hA : A.ASRegular Q) (hB : B.ASRegular Q) (i j : ℤ) :
    Module.finrank k (A.Hom i j) = Module.finrank k (B.Hom i j) :=
  A.component_finrank_eq_of_ASResolutions B Q hA.1 hB.1 i j

end ASGinzburg.ZAlgebra
