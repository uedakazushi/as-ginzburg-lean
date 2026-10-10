import work.ASGinzburgDraft.PeriodCutForgetColimits
import work.ASGinzburgDraft.PeriodCutOrdinaryProjectives
import ASGinzburg.RightModuleEnoughProjectives
import ASGinzburg.FiniteProjectiveDuality
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves

/-! Arbitrary native-small sums of actual representables remain ordinary
projective modules. Every projective cover module splits from its actual
free representable cover, so the functor preserves all projective objects. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

theorem cornerRepresentableSum_ring_projective {I : Type v} (i : I→ℤ) :
    Projective ((E.cornerModuleRingFunctor Q).obj
      (∐ fun j : I => (E.cornerCoverZAlgebra Q).representable (i j))) := by
  letI : ∀ j : I,Projective ((E.cornerModuleRingFunctor Q).obj
      ((E.cornerCoverZAlgebra Q).representable (i j))) :=
    fun j => E.cornerRepresentable_ring_projective Q (i j)
  let e := PreservesCoproduct.iso (E.cornerModuleRingFunctor Q)
    (fun j : I => (E.cornerCoverZAlgebra Q).representable (i j))
  exact Projective.of_iso e.symm (ASGinzburg.coproduct_projective
    (fun j : I => (E.cornerModuleRingFunctor Q).obj
      ((E.cornerCoverZAlgebra Q).representable (i j))))

theorem cornerFreeRightModule_ring_projective
    (M : (E.cornerCoverZAlgebra Q).RightModule) :
    Projective ((E.cornerModuleRingFunctor Q).obj
      ((E.cornerCoverZAlgebra Q).freeRightModule M)) := by
  change Projective ((E.cornerModuleRingFunctor Q).obj
    (∐ fun j : (E.cornerCoverZAlgebra Q).rightModuleGenerators M =>
      (E.cornerCoverZAlgebra Q).representable j.1))
  exact E.cornerRepresentableSum_ring_projective Q
    (I:=(E.cornerCoverZAlgebra Q).rightModuleGenerators M) (fun j => j.1)

theorem cornerProjective_ring_projective
    (P : (E.cornerCoverZAlgebra Q).RightModule) [Projective P] :
    Projective ((E.cornerModuleRingFunctor Q).obj P) := by
  let C := E.cornerCoverZAlgebra Q
  let r : Retract P (C.freeRightModule P) := {
    i := Projective.factorThru (𝟙 P) (C.freeRightModuleπ P)
    r := C.freeRightModuleπ P
    retract := Projective.factorThru_comp (𝟙 P) (C.freeRightModuleπ P)
  }
  letI := E.cornerFreeRightModule_ring_projective Q P
  exact ASGinzburg.projective_of_retract (r.map (E.cornerModuleRingFunctor Q))

instance cornerModuleRingFunctorPreservesProjectiveObjects :
    (E.cornerModuleRingFunctor Q).PreservesProjectiveObjects where
  projective_obj hP := by
    letI := hP
    exact E.cornerProjective_ring_projective Q _

end ASGinzburg.ZAlgebra.PeriodIso
