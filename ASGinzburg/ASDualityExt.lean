import ASGinzburg.ASResolutionSyzygies
import ASGinzburg.ASDualityHomTerms
import ASGinzburg.ASRegular

/-!
# The actual nonzero Ext in Proposition 1.3

Three concrete syzygy short exact sequences and mathlib's long exact Ext
sequence give Ext^3(s_(tau v),P_v) ≃ k. No Ext comparison is assumed.
This is one nonzero position, not the whole AS duality or periodicity theorem.
-/

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def ASResolution.asDualityExtThreeEquiv (v : Q.LiftVertex)
    (R : A.ASResolution Q (Q.tau v)) :
    Abelian.Ext.{v} (A.simpleRightModule (Q.height (Q.tau v)))
      (A.representable (Q.height v)) 3 ≃ₗ[k] k := by
  let N := A.representable (Q.height v)
  let e₂ := A.rightModuleExtZeroDimensionShift R.shortExact₂ N
    (A.asDualityHomTerm₂_zero Q v)
  let e₁ := A.rightModuleExtDimensionShift R.shortExact₁ N 0
  let e₀ := A.rightModuleExtDimensionShift
    (ASResolution.shortExact₀ (A := A) (Q := Q) (v := Q.tau v)) N 1
  exact ((e₂.trans e₁).trans e₀).symm.trans
    ((A.rightModuleExtZeroLinearEquiv _ _).trans (A.asDualityHomTerm₃Equiv Q v))

noncomputable def ASRegular.extThreeEquiv (h : A.ASRegular Q) (v : Q.LiftVertex) :
    Abelian.Ext.{v} (A.simpleRightModule (Q.height (Q.tau v)))
      (A.representable (Q.height v)) 3 ≃ₗ[k] k :=
  (h.resolution A Q (Q.tau v)).asDualityExtThreeEquiv A Q v

theorem ASRegular.extThree_finrank (h : A.ASRegular Q) (v : Q.LiftVertex) :
    Module.finrank k (Abelian.Ext.{v} (A.simpleRightModule (Q.height (Q.tau v)))
      (A.representable (Q.height v)) 3) = 1 :=
  (h.extThreeEquiv A Q v).finrank_eq.trans (Module.finrank_self k)

theorem ASRegular.extThree_rank (h : A.ASRegular Q) (v : Q.LiftVertex) :
    Module.rank k (Abelian.Ext.{v} (A.simpleRightModule (Q.height (Q.tau v)))
      (A.representable (Q.height v)) 3) = 1 := by
  letI := h.extFinite A Q v (Q.tau v) 3
  rw [← Module.finrank_eq_rank, h.extThree_finrank A Q v]
  rfl

end ASGinzburg.ZAlgebra
