import work.ASGinzburgDraft.PeriodCutGradedNakayama
import work.ASGinzburgDraft.BalancedTensorQuotient
import work.ASGinzburgDraft.BalancedTensorScalarRestriction

/-! For an actual bounded-below graded module, tensoring with the native
semisimple radical quotient detects the zero module. The tensor product
is the balancing quotient already constructed, and the radical comes
from the original graded cut algebra. -/
namespace ASGinzburg.ZAlgebra.PeriodIso.CutGradedRightModule
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable {Q : CutQuiver} {E : A.PeriodIso (Q.vertices:ℤ)}

theorem balancedTensorIdealAction_eq_gradedRadicalActionSpan
    (M : E.CutGradedRightModule Q) :
    balancedTensorIdealAction k
      (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ))) M.space (E.cutGradedJacobson Q) =
        M.gradedRadicalActionSpan := by
  unfold balancedTensorIdealAction gradedRadicalActionSpan
  congr 1
  ext y
  constructor
  · rintro ⟨⟨r, x⟩, rfl⟩
    exact ⟨r, r.property, x, rfl⟩
  · rintro ⟨r, hr, x, hx⟩
    exact ⟨(⟨r, hr⟩, x), hx⟩

theorem subsingleton_space_of_grade_lower_bound_tensor_radical_quotient
    (M : E.CutGradedRightModule Q) (b : ℤ)
    (hb : ∀ q : ℤ, q < b → M.grade q = ⊥)
    (hT : Subsingleton (BalancedTensorSpace k
      (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ))) M.space
      (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)) ⧸ E.cutGradedJacobson Q))) :
    Subsingleton M.space := by
  let e := balancedTensorQuotientEquiv k
    (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ))) M.space (E.cutGradedJacobson Q)
  have hQ : Subsingleton (M.space ⧸ balancedTensorIdealAction k
      (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ))) M.space (E.cutGradedJacobson Q)) :=
    ⟨fun x y => e.symm.injective (hT.elim _ _)⟩
  rw [M.balancedTensorIdealAction_eq_gradedRadicalActionSpan] at hQ
  exact M.subsingleton_space_of_grade_lower_bound_radical_quotient b hb hQ

theorem ringModule_isZero_of_grade_lower_bound_tensor_radical_quotient
    (M : E.CutGradedRightModule Q) (b : ℤ)
    (hb : ∀ q : ℤ, q < b → M.grade q = ⊥)
    (hT : IsZero (ModuleCat.of k (BalancedTensorSpace k
      (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ))) M.space
      (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)) ⧸ E.cutGradedJacobson Q)))) :
    IsZero M.ringModule :=
  ModuleCat.isZero_iff_subsingleton.mpr
    (M.subsingleton_space_of_grade_lower_bound_tensor_radical_quotient b hb
      (ModuleCat.isZero_iff_subsingleton.mp hT))


theorem ringModule_isZero_of_grade_lower_bound_tensor_functor
    (M : E.CutGradedRightModule Q) (b : ℤ)
    (hb : ∀ q : ℤ, q < b → M.grade q = ⊥)
    (hT : IsZero ((balancedTensorLeftFunctor k
      (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))
      (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)) ⧸ E.cutGradedJacobson Q)).obj
        M.ringModule)) : IsZero M.ringModule := by
  have hOriginal := (balancedTensorScalarRestrictionIso k
    (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ))) M.space
    (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)) ⧸ E.cutGradedJacobson Q)).isZero_iff.mp hT
  exact M.ringModule_isZero_of_grade_lower_bound_tensor_radical_quotient b hb hOriginal

end ASGinzburg.ZAlgebra.PeriodIso.CutGradedRightModule
