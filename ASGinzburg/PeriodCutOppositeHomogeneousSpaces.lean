import ASGinzburg.PeriodCutOrdinaryGradedNakayama

/-! The actual opposite cut-ring grading is exactly the original grading
under unop, including all natural and negative internal degrees. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

theorem cutIntegerOppositeHomogeneousSpace_mem_iff_unop (q : ℤ)
    (r : (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))ᵐᵒᵖ) :
    r ∈ E.cutIntegerOppositeHomogeneousSpace Q q ↔
      r.unop ∈ E.cutIntegerHomogeneousSpace Q q := by
  change (∃ x, x ∈ E.cutIntegerHomogeneousSpace Q q ∧ MulOpposite.op x=r) ↔ _
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact hx
  · intro hr
    exact ⟨r.unop,hr,MulOpposite.op_unop r⟩

theorem cutIntegerOppositeHomogeneousSpace_ofNat (n : ℕ) :
    E.cutIntegerOppositeHomogeneousSpace Q (n:ℤ) =
      (LinearMap.range (E.cutHomogeneousLinearInclusion
        (fun i : Q.Vertex => (i.val:ℤ)) n)).map (MulOpposite.opLinearEquiv k).toLinearMap := by
  rw [cutIntegerOppositeHomogeneousSpace,E.cutIntegerHomogeneousSpace_ofNat]

theorem cutIntegerOppositeHomogeneousSpace_negative {q : ℤ} (hq : q<0) :
    E.cutIntegerOppositeHomogeneousSpace Q q=⊥ := by
  rw [cutIntegerOppositeHomogeneousSpace,E.cutIntegerHomogeneousSpace_negative Q hq,
    Submodule.map_bot]

end ASGinzburg.ZAlgebra.PeriodIso
