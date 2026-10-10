import ASGinzburg.PeriodCutCornerFieldTotalNaturality
import ASGinzburg.PeriodCutForgetGrading
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import ASGinzburg.AlgebraModuleRestrictionComparison

/-! Forgetting the actual right R-action down to k recovers the same
component direct sum, with its original scalar action and actual maps. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices : ℤ))

instance cutGradedForgetFunctorFaithful : (E.cutGradedForgetFunctor Q).Faithful where
  map_injective := by
    intro M N f g h
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun t => t.hom x) h

instance cornerModuleRingFunctorFaithful : (E.cornerModuleRingFunctor Q).Faithful := by
  dsimp [cornerModuleRingFunctor]
  infer_instance

noncomputable def cornerRingScalarObjIso
    (M : (E.cornerCoverZAlgebra Q).RightModule) :
    (ModuleCat.restrictScalars (algebraMap k
      (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))ᵐᵒᵖ)).obj
      ((E.cornerModuleRingFunctor Q).obj M) ≅
    (E.cornerTotalSpaceFunctor Q).obj M := by
  let N := E.cornerGradedRightModule Q M
  letI := N.rightModule
  letI := N.scalarTower
  exact algebraModuleRestrictScalarsIso k
    (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))ᵐᵒᵖ
    N.space

noncomputable def cornerRingScalarNatIso :
    E.cornerModuleRingFunctor Q ⋙
      ModuleCat.restrictScalars (algebraMap k
        (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))ᵐᵒᵖ) ≅
      E.cornerTotalSpaceFunctor Q :=
  NatIso.ofComponents (E.cornerRingScalarObjIso Q) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl)

end ASGinzburg.ZAlgebra.PeriodIso
