import ASGinzburg.QuadraticResolutionComponents
import ASGinzburg.TriangleQuadraticASRegular
import ASGinzburg.Hilbert

/-! The actual component Hilbert function and polynomial growth follow
from the exact quadratic resolutions, using the Euler identity proved from
their evaluation. No recurrence or periodicity is assumed. -/

namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

theorem hom_finrank_eq_zero_of_lt (i j : ℤ) (hji : j < i) :
    Module.finrank k (A.Hom i j) = 0 := by
  letI : Subsingleton (A.Hom i j) := ⟨fun x y => by rw [A.positive hji x, A.positive hji y]⟩
  exact Module.finrank_zero_of_subsingleton

theorem hom_diagonal_finrank (i : ℤ) : Module.finrank k (A.Hom i i) = 1 := by
  rw [← (A.scalarEndEquiv i).finrank_eq]
  exact Module.finrank_self k

/-- Source §5's actual Hilbert function, already from condition (5.1). -/
theorem component_finrank_of_quadraticASResolutions
    (hres : ∀ i : ℤ, Nonempty (A.QuadraticASResolution i)) (i : ℤ) (m : ℕ) :
    Module.finrank k (A.Hom i (i + m)) = Nat.choose (m + 2) 2 := by
  let dim : ℤ → ℕ := fun j => Module.finrank k (A.Hom i j)
  let h : ℕ → ℤ := fun n => dim (i + n)
  have h₀ : h 0 = 1 := by
    change (dim (i + 0) : ℤ) = 1
    rw [add_zero]
    have hd : dim i = 1 := A.hom_diagonal_finrank i
    exact_mod_cast hd
  have h₁ : h 1 = 3 := by
    have e := (Classical.choice (hres (i + 1))).component_euler i
    change (dim (i + 1) : ℤ) - 3 * dim ((i + 1) - 1) +
      3 * dim ((i + 1) - 2) - dim ((i + 1) - 3) = if i = i + 1 then 1 else 0 at e
    have e₁ : (i + 1) - 1 = i := by omega
    have z₂ := A.hom_finrank_eq_zero_of_lt i ((i + 1) - 2) (by omega)
    have z₃ := A.hom_finrank_eq_zero_of_lt i ((i + 1) - 3) (by omega)
    have hd₀ : dim i = 1 := A.hom_diagonal_finrank i
    have hd₂ : dim ((i + 1) - 2) = 0 := z₂
    have hd₃ : dim ((i + 1) - 3) = 0 := z₃
    rw [e₁, hd₀, hd₂, hd₃, if_neg (by omega : i ≠ i + 1)] at e
    change (dim (i + 1) : ℤ) = 3
    omega
  have h₂ : h 2 = 6 := by
    have e := (Classical.choice (hres (i + 2))).component_euler i
    change (dim (i + 2) : ℤ) - 3 * dim ((i + 2) - 1) +
      3 * dim ((i + 2) - 2) - dim ((i + 2) - 3) = if i = i + 2 then 1 else 0 at e
    have e₁ : (i + 2) - 1 = i + 1 := by omega
    have e₂ : (i + 2) - 2 = i := by omega
    have z₃ := A.hom_finrank_eq_zero_of_lt i ((i + 2) - 3) (by omega)
    have hd₀ : dim i = 1 := A.hom_diagonal_finrank i
    have hd₃ : dim ((i + 2) - 3) = 0 := z₃
    rw [e₁, e₂, hd₀, hd₃, if_neg (by omega : i ≠ i + 2)] at e
    change (dim (i + 1) : ℤ) = 3 at h₁
    change (dim (i + 2) : ℤ) = 6
    omega
  have hrec : ∀ n, h (n + 3) - 3 * h (n + 2) + 3 * h (n + 1) - h n = 0 := by
    intro n
    have e := (Classical.choice (hres (i + (n + 3 : ℕ)))).component_euler i
    change (dim (i + (n + 3 : ℕ)) : ℤ) - 3 * dim ((i + (n + 3 : ℕ)) - 1) +
      3 * dim ((i + (n + 3 : ℕ)) - 2) - dim ((i + (n + 3 : ℕ)) - 3) =
      if i = i + (n + 3 : ℕ) then 1 else 0 at e
    have e₁ : (i + (n + 3 : ℕ)) - 1 = i + (n + 2 : ℕ) := by omega
    have e₂ : (i + (n + 3 : ℕ)) - 2 = i + (n + 1 : ℕ) := by omega
    have e₃ : (i + (n + 3 : ℕ)) - 3 = i + (n : ℕ) := by omega
    rw [e₁, e₂, e₃, if_neg (by omega : i ≠ i + (n + 3 : ℕ))] at e
    exact e
  have hm := quadraticHilbert_unique h h₀ h₁ h₂ hrec m
  change (Module.finrank k (A.Hom i (i + m)) : ℤ) = (Nat.choose (m + 2) 2 : ℤ) at hm
  exact_mod_cast hm

theorem QuadraticASRegular.component_finrank (hAS : A.QuadraticASRegular) (i : ℤ) (m : ℕ) :
    Module.finrank k (A.Hom i (i + m)) = Nat.choose (m + 2) 2 :=
  A.component_finrank_of_quadraticASResolutions hAS.1 i m

theorem QuadraticASRegular.component_finrank_sub (hAS : A.QuadraticASRegular) (i : ℤ) (m : ℕ) :
    Module.finrank k (A.Hom (i - m) i) = Nat.choose (m + 2) 2 := by
  have h := hAS.component_finrank A (i - m) m
  have e : (i - (m : ℤ)) + m = i := by omega
  exact (congrArg (fun j => Module.finrank k (A.Hom (i - m) j)) e).symm.trans h

theorem QuadraticASRegular.component_polynomial_bound (hAS : A.QuadraticASRegular)
    (i : ℤ) (m : ℕ) :
    Module.finrank k (A.Hom i (i + m)) ≤ (m + 2) ^ 2 := by
  rw [hAS.component_finrank A]
  exact quadraticHilbert_polynomial_bound m

/-- Accumulated actual component dimensions have cubic polynomial growth. -/
theorem QuadraticASRegular.cumulative_polynomial_bound (hAS : A.QuadraticASRegular)
    (i : ℤ) (n : ℕ) :
    (∑ m ∈ Finset.range (n + 1), Module.finrank k (A.Hom i (i + m))) ≤ (n + 2) ^ 3 := by
  calc
    (∑ m ∈ Finset.range (n + 1), Module.finrank k (A.Hom i (i + m))) ≤
        ∑ _m ∈ Finset.range (n + 1), (n + 2) ^ 2 := by
      apply Finset.sum_le_sum
      intro m hm
      have hmn : m ≤ n := by have := Finset.mem_range.mp hm; omega
      exact (hAS.component_polynomial_bound A i m).trans
        (Nat.pow_le_pow_left (by omega : m + 2 ≤ n + 2) 2)
    _ = (n + 1) * (n + 2) ^ 2 := by simp
    _ ≤ (n + 2) ^ 3 := by nlinarith

end ASGinzburg.ZAlgebra
