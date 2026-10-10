import Mathlib.Algebra.Homology.BifunctorFlip

/-! Genuine total-complex symmetry for natural-number chain complexes.
The sign on bidegree (p,q) is the actual Koszul sign (-1)^(pq). -/
namespace ASGinzburg

instance natDownTotalComplexShapeSymmetry :
    TotalComplexShapeSymmetry (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) where
  symm p q := Nat.add_comm q p
  σ p q := (-1 : ℤˣ) ^ (p*q)
  σ_ε₁ := by
    rintro _ p rfl q
    change (-1 : ℤˣ)^((p+1)*q) * 1 = (-1 : ℤˣ)^q * (-1 : ℤˣ)^(p*q)
    simp only [Nat.add_mul, one_mul, pow_add, mul_one]
    exact mul_comm _ _
  σ_ε₂ := by
    rintro p _ q rfl
    change (-1 : ℤˣ)^(p*(q+1)) * (-1 : ℤˣ)^p = 1 * (-1 : ℤˣ)^(p*q)
    rw [Nat.mul_add, Nat.mul_one, pow_add, one_mul, mul_assoc,
      Int.units_mul_self, mul_one]

instance natDownTotalComplexShapeSymmetrySymmetry :
    TotalComplexShapeSymmetrySymmetry (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) where
  σ_symm p q := by
    change (-1 : ℤˣ)^(q*p) = (-1 : ℤˣ)^(p*q)
    rw [Nat.mul_comm]

end ASGinzburg
