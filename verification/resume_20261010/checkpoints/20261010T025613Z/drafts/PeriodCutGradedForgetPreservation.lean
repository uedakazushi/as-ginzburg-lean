import work.ASGinzburgDraft.PeriodCutGradedForgetExactness
import work.ASGinzburgDraft.PeriodCutOrdinaryProjectivePreservation

/-! Forgetting the genuine integer grading preserves all native-small
colimits and all projective objects, through the actual cover equivalence
and the proved splitting of cover projectives from representable sums. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

noncomputable instance cutGradedForgetFunctorPreservesColimits :
    PreservesColimitsOfSize.{v,v} (E.cutGradedForgetFunctor Q) :=
  preservesColimits_of_natIso (E.recoveredRingForgetNatIso Q)

instance cutGradedForgetFunctorPreservesProjectiveObjects :
    (E.cutGradedForgetFunctor Q).PreservesProjectiveObjects where
  projective_obj {M} hM := by
    letI := hM
    exact Projective.of_iso ((E.recoveredRingForgetNatIso Q).app M) inferInstance

end ASGinzburg.ZAlgebra.PeriodIso
