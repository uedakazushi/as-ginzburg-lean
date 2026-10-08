import ASGinzburg.ASResolutionSyzygies

/-!
# Actual Ext bounds from the finite AS sequence alone

The short exact syzygy sequences imply vanishing above degree three for
every target. The total AS dimension condition is not used.
-/

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

namespace ASResolution
variable {A} {Q : CutQuiver} {w : Q.LiftVertex}

/-- Three shifts along the actual finite sequence, with arbitrary target. -/
noncomputable def extShiftThree (R : A.ASResolution Q w) (N : A.RightModule) (n : ℕ) :
    Abelian.Ext.{v} (A.representable (Q.height (Q.tau.symm w))) N (n + 1) ≃ₗ[k]
      Abelian.Ext.{v} (A.simpleRightModule (Q.height w)) N (n + 4) :=
  ((A.rightModuleExtDimensionShift R.shortExact₂ N n).trans
    (A.rightModuleExtDimensionShift R.shortExact₁ N (n + 1))).trans
      (A.rightModuleExtDimensionShift
        (ASResolution.shortExact₀ (A := A) (Q := Q) (v := w)) N (n + 2))

theorem ext_ge_four_eq_zero (R : A.ASResolution Q w) (N : A.RightModule) (n : ℕ)
    (e : Abelian.Ext.{v} (A.simpleRightModule (Q.height w)) N (n + 4)) : e = 0 := by
  obtain ⟨x, rfl⟩ := (R.extShiftThree N n).surjective e
  rw [A.representable_higher_ext_eq_zero _ _ _ x, LinearEquiv.map_zero]

theorem ext_ge_four_rank_zero (R : A.ASResolution Q w) (N : A.RightModule) (n : ℕ) :
    Module.rank k (Abelian.Ext.{v} (A.simpleRightModule (Q.height w)) N (n + 4)) = 0 := by
  letI : Subsingleton (Abelian.Ext.{v} (A.simpleRightModule (Q.height w)) N (n + 4)) :=
    ⟨fun x y => by rw [R.ext_ge_four_eq_zero N n x, R.ext_ge_four_eq_zero N n y]⟩
  exact rank_subsingleton' k _

end ASResolution
end ASGinzburg.ZAlgebra
