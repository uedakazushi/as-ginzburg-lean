import work.ASGinzburgDraft.PeriodCutOrdinaryRingDualShiftedHomNaturality

/-! Actual graded Hom exactness yields exactness of each genuine
homogeneous ordinary ring-dual component. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))
variable {L M N : E.CutGradedRightModule Q}
local notation "R" => (E.CutGradedRing (fun i : Q.Vertex => (Fin.val i:ℤ)))ᵐᵒᵖ

 theorem cutOrdinaryRingDual_homogeneous_cycle_eq_zero
    (a : N ⟶ M) (q : ℤ) (f : (E.cutRightModuleOrdinaryData Q M).ringDualGrade q)
    (hf : ordinaryRingDualMap R ((E.cutGradedForgetFunctor Q).map a) f.val = 0)
    (hExact : ∀ g : M ⟶ (E.cutRegularGradedRightModule Q).shifted q,
      a ≫ g = 0 → g = 0) : f.val = 0 := by
  have hc : a ≫ E.cutOrdinaryRingDualShiftedHomEquiv Q M q f = 0 := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change (f.val (a.val x)).unop = 0
    have hx := LinearMap.congr_fun hf x
    change f.val (a.val x) = 0 at hx
    simpa only [MulOpposite.unop_zero] using congrArg MulOpposite.unop hx
  have hz : f = 0 := (E.cutOrdinaryRingDualShiftedHomEquiv Q M q).injective
    (by simpa only [map_zero] using hExact _ hc)
  exact congrArg Subtype.val hz

 theorem cutOrdinaryRingDual_homogeneous_boundary
    (a : M ⟶ L) (b : N ⟶ M) (q : ℤ)
    (f : (E.cutRightModuleOrdinaryData Q M).ringDualGrade q)
    (hf : ordinaryRingDualMap R ((E.cutGradedForgetFunctor Q).map b) f.val = 0)
    (hExact : ∀ g : M ⟶ (E.cutRegularGradedRightModule Q).shifted q,
      b ≫ g = 0 → ∃ h : L ⟶ (E.cutRegularGradedRightModule Q).shifted q,
        a ≫ h = g) :
    ∃ h : ordinaryRingDual R (E.cutRightModuleOrdinaryData Q L).ringModule,
      ordinaryRingDualMap R ((E.cutGradedForgetFunctor Q).map a) h = f.val := by
  have hc : b ≫ E.cutOrdinaryRingDualShiftedHomEquiv Q M q f = 0 := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change (f.val (b.val x)).unop = 0
    have hx := LinearMap.congr_fun hf x
    change f.val (b.val x) = 0 at hx
    simpa only [MulOpposite.unop_zero] using congrArg MulOpposite.unop hx
  obtain ⟨g,hg⟩ := hExact _ hc
  let h := (E.cutOrdinaryRingDualShiftedHomEquiv Q L q).symm g
  refine ⟨h.val, ?_⟩
  have he := E.cutOrdinaryRingDualShiftedHomEquiv_precomp Q a q h
  rw [show E.cutOrdinaryRingDualShiftedHomEquiv Q L q h = g from
    LinearEquiv.apply_symm_apply _ _, hg] at he
  exact congrArg Subtype.val ((E.cutOrdinaryRingDualShiftedHomEquiv Q M q).injective he)

end ASGinzburg.ZAlgebra.PeriodIso
