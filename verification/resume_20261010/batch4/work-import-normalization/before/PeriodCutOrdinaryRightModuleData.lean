import work.ASGinzburgDraft.PeriodCutOrdinaryGradedNakayama
import ASGinzburg.PeriodCutForgetGrading
import ASGinzburg.AlgebraModuleRestrictionComparison

/-! The native right-module grading remains an actual internal grading
after using the canonical field action of its ordinary module object. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory
open scoped DirectSum ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices : ℤ))

noncomputable def cutRightModuleOrdinaryGrade (N : E.CutGradedRightModule Q) (q : ℤ) :
    Submodule k N.ringModule :=
  (N.grade q).comap (algebraModuleRestrictScalarsIso k
    (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))ᵐᵒᵖ N.space).hom.hom

theorem cutRightModuleOrdinaryGrade_mem (N : E.CutGradedRightModule Q)
    (q : ℤ) (x : N.ringModule) :
    x ∈ E.cutRightModuleOrdinaryGrade Q N q ↔ (x : N.space) ∈ N.grade q := Iff.rfl

noncomputable def cutRightModuleOrdinaryData (N : E.CutGradedRightModule Q) :
    GradedOrdinaryModuleData k
      (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))ᵐᵒᵖ
      (E.cutIntegerOppositeHomogeneousSpace Q) where
  ringModule := N.ringModule
  grade := E.cutRightModuleOrdinaryGrade Q N
  isInternal := by
    letI : DirectSum.Decomposition (E.cutRightModuleOrdinaryGrade Q N) := {
      decompose' := N.decomposition.decompose'
      left_inv := N.decomposition.left_inv
      right_inv := N.decomposition.right_inv
    }
    exact DirectSum.Decomposition.isInternal _
  smul_mem := by
    intro p q r hr x hx
    obtain ⟨s, hs, rfl⟩ := hr
    by_cases hp : 0 ≤ p
    · rw [cutIntegerHomogeneousSpace, if_pos hp] at hs
      obtain ⟨a, rfl⟩ := hs
      have ht : (p.toNat : ℤ) = p := Int.toNat_of_nonneg hp
      change (N.representation
        (E.cutHomogeneousInclusion (fun i : Q.Vertex => (i.val : ℤ)) p.toNat a)).unop x ∈
          N.grade (p + q)
      simpa only [ht, add_comm] using N.homogeneous p.toNat a q x hx
    · rw [E.cutIntegerHomogeneousSpace_negative Q (by omega)] at hs
      have hs0 : s = 0 := by simpa only [Submodule.mem_bot] using hs
      subst s
      change (MulOpposite.op (0 : E.CutGradedRing _)) • x ∈ _
      rw [MulOpposite.op_zero, zero_smul]
      exact Submodule.zero_mem _

theorem cutRightModuleOrdinaryData_boundedBelow (N : E.CutGradedRightModule Q)
    (b : ℤ) (hb : ∀ q : ℤ, q < b → N.grade q = ⊥) :
    (E.cutRightModuleOrdinaryData Q N).BoundedBelow b := by
  intro q hq
  simp only [cutRightModuleOrdinaryData, cutRightModuleOrdinaryGrade, hb q hq,
    Submodule.comap_bot]
  exact LinearMap.ker_eq_bot.mpr
    (algebraModuleRestrictScalarsIso k
      (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))ᵐᵒᵖ N.space).toLinearEquiv.injective

theorem cutRightModuleOrdinaryMap_preservesGrade
    {N P : E.CutGradedRightModule Q} (f : N ⟶ P) :
    (E.cutRightModuleOrdinaryData Q N).PreservesGrade
      (E.cutRightModuleOrdinaryData Q P) ((E.cutGradedForgetFunctor Q).map f) :=
  fun q x hx => f.property.2 q x hx

end ASGinzburg.ZAlgebra.PeriodIso
