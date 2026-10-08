import ASGinzburg.SimpleVectorDuality
import ASGinzburg.FiniteDimensionalNakayama

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

noncomputable def rightFiniteDimensionalSimple (i : ℤ) : A.RightFiniteDimensional :=
  ⟨A.simpleRightModule i,A.rightFiniteDimensional_simple i⟩
noncomputable def leftFiniteDimensionalSimple (i : ℤ) : A.LeftFiniteDimensional :=
  ⟨A.simpleLeftModule i,A.leftFiniteDimensional_simple i⟩

noncomputable def leftFiniteDimensionalSimpleVectorDualIso (i : ℤ) :
    A.leftFiniteDimensionalVectorDualFunctor.obj (op (A.leftFiniteDimensionalSimple i)) ≅
      A.rightFiniteDimensionalSimple i :=
  A.rightFiniteDimensionalProperty.isoMk (A.leftSimpleVectorDualIso i)

noncomputable def rightFiniteDimensionalExtThreeSimpleIso (Q : CutQuiver) (hAS : A.ASRegular Q)
    (w : Q.LiftVertex) :
    (A.rightFiniteDimensionalExtThreeFunctor Q hAS).obj (op (A.rightFiniteDimensionalSimple (Q.height w))) ≅
      A.leftFiniteDimensionalSimple (Q.height (Q.tau.symm w)) :=
  A.leftFiniteDimensionalProperty.isoMk (hAS.extLeftThreeIsoSimple A Q w)

noncomputable def rightFiniteDimensionalNakayamaSimpleIso (Q : CutQuiver) (hAS : A.ASRegular Q)
    (w : Q.LiftVertex) :
    (A.rightFiniteDimensionalNakayamaEquivalence Q hAS).functor.obj
        (A.rightFiniteDimensionalSimple (Q.height w)) ≅
      A.rightFiniteDimensionalSimple (Q.height (Q.tau.symm w)) :=
  (A.leftFiniteDimensionalVectorDualFunctor.mapIso
    (A.rightFiniteDimensionalExtThreeSimpleIso Q hAS w).op).symm ≪≫
      A.leftFiniteDimensionalSimpleVectorDualIso _

noncomputable def rightFiniteDimensionalNakayamaSimpleHeightIso (Q : CutQuiver) (hAS : A.ASRegular Q)
    (i : ℤ) :
    (A.rightFiniteDimensionalNakayamaEquivalence Q hAS).functor.obj (A.rightFiniteDimensionalSimple i) ≅
      A.rightFiniteDimensionalSimple (i - Q.vertices) := by
  let w := Q.heightEquiv.symm i
  have hw : Q.height w = i := by
    rw [← Q.heightEquiv_apply]
    exact Q.heightEquiv.apply_symm_apply i
  have ht : Q.height (Q.tau.symm w) = i-Q.vertices := by
    have H := Q.height_tau (Q.tau.symm w)
    rw [Q.tau.apply_symm_apply,hw] at H
    omega
  simpa only [hw,ht] using A.rightFiniteDimensionalNakayamaSimpleIso Q hAS w
end ASGinzburg.ZAlgebra
