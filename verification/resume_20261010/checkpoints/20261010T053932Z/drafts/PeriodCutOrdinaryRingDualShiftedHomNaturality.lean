import work.ASGinzburgDraft.PeriodCutOrdinaryRingDualShiftedHom

/-! The actual ordinary-ring dual and the actual graded shifted Hom
comparison intertwine precomposition by every genuine graded map. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))
variable {M N : E.CutGradedRightModule Q}

theorem cutOrdinaryRingDual_precomp_mem_grade (g : M ⟶ N) (q : ℤ)
    (f : (E.cutRightModuleOrdinaryData Q N).ringDualGrade q) :
    ordinaryRingDualMap
      (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))ᵐᵒᵖ
      ((E.cutGradedForgetFunctor Q).map g) f.val ∈
      (E.cutRightModuleOrdinaryData Q M).ringDualGrade q :=
  (E.cutRightModuleOrdinaryData Q M).ringDualMap_preservesGrade
    (E.cutRightModuleOrdinaryData Q N) ((E.cutGradedForgetFunctor Q).map g)
    (E.cutRightModuleOrdinaryMap_preservesGrade Q g) q f.val f.property

theorem cutOrdinaryRingDualShiftedHomEquiv_precomp (g : M ⟶ N) (q : ℤ)
    (f : (E.cutRightModuleOrdinaryData Q N).ringDualGrade q) :
    E.cutOrdinaryRingDualShiftedHomEquiv Q M q
      ⟨ordinaryRingDualMap
        (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))ᵐᵒᵖ
        ((E.cutGradedForgetFunctor Q).map g) f.val,
        E.cutOrdinaryRingDual_precomp_mem_grade Q g q f⟩ =
      g ≫ E.cutOrdinaryRingDualShiftedHomEquiv Q N q f := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  rfl

end ASGinzburg.ZAlgebra.PeriodIso
