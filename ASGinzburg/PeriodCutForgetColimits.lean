import ASGinzburg.PeriodCutForgetScalarComparison
import ASGinzburg.ModuleCatRestrictionColimits
import ASGinzburg.RightModuleColimitPreservation

/-! The actual cover-to-ordinary-module functor preserves every small
colimit in the native Hom universe. Its scalar restriction is the
discrete colimit of the genuine component evaluations. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

noncomputable instance cornerFieldTotalFunctorPreservesColimits :
    PreservesColimitsOfSize.{v,v} (E.cornerFieldTotalFunctor Q) := by
  letI : PreservesColimitsOfSize.{v,v}
      (colim : (Discrete Q.LiftVertex ⥤ ModuleCat.{v} k) ⥤ ModuleCat.{v} k) :=
    colimConstAdj.leftAdjoint_preservesColimits
  dsimp [cornerFieldTotalFunctor,cornerFieldComponents]
  infer_instance

noncomputable instance cornerTotalSpaceFunctorPreservesColimits :
    PreservesColimitsOfSize.{v,v} (E.cornerTotalSpaceFunctor Q) :=
  preservesColimits_of_natIso (E.cornerFieldTotalNatIso Q)

noncomputable instance cornerModuleRingFunctorPreservesColimits :
    PreservesColimitsOfSize.{v,v} (E.cornerModuleRingFunctor Q) := by
  let R := (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))ᵐᵒᵖ
  let G := ModuleCat.restrictScalars (algebraMap k R)
  letI : ReflectsColimitsOfSize.{v,v} G :=
    moduleCatRestrictionReflectsSmallColimits (algebraMap k R)
  letI : PreservesColimitsOfSize.{v,v} (E.cornerModuleRingFunctor Q ⋙ G) :=
    preservesColimits_of_natIso (E.cornerRingScalarNatIso Q).symm
  exact preservesColimits_of_reflects_of_preserves (E.cornerModuleRingFunctor Q) G

end ASGinzburg.ZAlgebra.PeriodIso
