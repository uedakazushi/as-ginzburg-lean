import Mathlib.Algebra.Module.Submodule.Map

/-! Pulling back a sum contained in a submodule along its genuine
subtype map preserves the sum. Used for the actual IJ+JI denominator. -/
namespace ASGinzburg
universe u v
variable {k : Type u} [Field k] {M : Type v} [AddCommGroup M] [Module k M]

theorem comap_subtype_sup_of_le (P p q : Submodule k M) (hp : p ≤ P) (hq : q ≤ P) :
    Submodule.comap P.subtype (p ⊔ q)=
      Submodule.comap P.subtype p ⊔ Submodule.comap P.subtype q := by
  apply Submodule.map_injective_of_injective (f := P.subtype) Subtype.val_injective
  simp only [Submodule.map_sup,Submodule.map_comap_subtype]
  rw [inf_eq_right.mpr (sup_le hp hq),inf_eq_right.mpr hp,inf_eq_right.mpr hq]

end ASGinzburg
