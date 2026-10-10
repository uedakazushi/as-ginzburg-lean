import Mathlib.RingTheory.Ideal.Operations

/-! The sum of actual two-sided nilpotent ideals is nilpotent in a
possibly noncommutative ring. The proof uses ideal multiplication and
its distributivity, without assuming commutativity of the ring. -/
namespace ASGinzburg
universe u
variable {R : Type u} [Semiring R]
variable (I J : Ideal R) [I.IsTwoSided] [J.IsTwoSided]

theorem noncommIdealSup_pow_le (n m : ℕ) :
    (I ⊔ J)^(n+m) ≤ I^n ⊔ J^m := by
  letI : (I ⊔ J).IsTwoSided := ⟨fun b ha => by
    obtain ⟨i, hi, j, hj, rfl⟩ := Submodule.mem_sup.mp ha
    rw [add_mul]
    exact Submodule.add_mem _
      ((show I ≤ I ⊔ J from le_sup_left) (I.mul_mem_right b hi))
      ((show J ≤ I ⊔ J from le_sup_right) (J.mul_mem_right b hj))⟩
  induction n generalizing m with
  | zero =>
    rw [Submodule.pow_zero, Ideal.one_eq_top, top_sup_eq]
    exact le_top
  | succ n ihn =>
    induction m with
    | zero =>
      rw [Submodule.pow_zero, Ideal.one_eq_top, sup_top_eq]
      exact le_top
    | succ m ihm =>
      have hleft : I*(I ⊔ J)^(n+(m+1)) ≤ I^(n+1) ⊔ J^(m+1) := by
        calc
          I*(I ⊔ J)^(n+(m+1)) ≤ I*(I^n ⊔ J^(m+1)) :=
            Ideal.mul_mono_right (ihn (m+1))
          _ = I*I^n ⊔ I*J^(m+1) := Ideal.mul_sup I (I^n) (J^(m+1))
          _ ≤ I^(n+1) ⊔ J^(m+1) := by
            rw [← Ideal.IsTwoSided.pow_succ]
            exact sup_le_sup le_rfl Ideal.mul_le_left
      have hright : J*(I ⊔ J)^((n+1)+m) ≤ I^(n+1) ⊔ J^(m+1) := by
        calc
          J*(I ⊔ J)^((n+1)+m) ≤ J*(I^(n+1) ⊔ J^m) :=
            Ideal.mul_mono_right ihm
          _ = J*I^(n+1) ⊔ J*J^m := Ideal.mul_sup J (I^(n+1)) (J^m)
          _ ≤ I^(n+1) ⊔ J^(m+1) := by
            rw [← Ideal.IsTwoSided.pow_succ]
            exact sup_le_sup Ideal.mul_le_left le_rfl
      have hindex : (n+1)+(m+1) = (n+(m+1))+1 := by omega
      rw [hindex, Ideal.IsTwoSided.pow_succ, Ideal.sup_mul]
      apply sup_le hleft
      convert hright using 1
      congr 2
      omega

theorem noncommIdealSup_pow_eq_bot (n m : ℕ)
    (hI : I^n=⊥) (hJ : J^m=⊥) : (I ⊔ J)^(n+m)=⊥ := by
  apply le_antisymm _ bot_le
  simpa only [hI,hJ,bot_sup_eq] using noncommIdealSup_pow_le I J n m

end ASGinzburg
