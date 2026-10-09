import ASGinzburg.GinzburgSquareProducts

/-! The triangular sign turns the reversed differential into a cochain map. -/
namespace ASGinzburg.CutQuiver
universe u
variable (k : Type u) [Field k]

noncomputable def ginzburgReflectionSign (q : ℤ) : k :=
  ginzburgSign k (q * (q + 1) / 2)

theorem ginzburgReflectionSign_ne_zero (q : ℤ) : ginzburgReflectionSign k q ≠ 0 :=
  zpow_ne_zero _ (neg_ne_zero.mpr (one_ne_zero : (1 : k) ≠ 0))

theorem ginzburgReflectionSign_mul_self (q : ℤ) :
    ginzburgReflectionSign k q * ginzburgReflectionSign k q = 1 :=
  ginzburgSign_mul_self k _

theorem ginzburgReflectionSign_succ (q : ℤ) :
    ginzburgReflectionSign k (q + 1) = ginzburgReflectionSign k q * ginzburgSign k (q + 1) := by
  unfold ginzburgReflectionSign
  rw [show (q + 1) * (q + 1 + 1) = q * (q + 1) + (q + 1) * 2 by ring,
    Int.add_mul_ediv_right _ _ (by decide), ginzburgSign_add]

theorem ginzburgReflectionSign_succ_mul (q : ℤ) :
    ginzburgReflectionSign k (q + 1) * ginzburgSign k (q + 1) = ginzburgReflectionSign k q := by
  rw [ginzburgReflectionSign_succ, mul_assoc, ginzburgSign_mul_self, mul_one]

end ASGinzburg.CutQuiver
