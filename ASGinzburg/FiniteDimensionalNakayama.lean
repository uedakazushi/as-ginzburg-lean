import ASGinzburg.FiniteDimensionalAbelian
import ASGinzburg.FiniteDimensionalVectorDuality
import ASGinzburg.FiniteDimensionalExtEquivalence

namespace ASGinzburg.ZAlgebra
open CategoryTheory Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

/-- The actual Ext³ followed by pointwise vector-space duality, under the original AS conditions. -/
noncomputable def rightFiniteDimensionalNakayamaEquivalence (Q : CutQuiver) (hAS : A.ASRegular Q) :
    A.RightFiniteDimensional ≌ A.RightFiniteDimensional :=
  (A.finiteDimensionalExtThreeEquivalence Q hAS).rightOp.trans A.leftFiniteDimensionalVectorDualEquivalence
end ASGinzburg.ZAlgebra

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

instance rightFiniteDimensionalExtThreeFunctorIsEquivalence (hAS : A.ASRegular Q) :
    (A.rightFiniteDimensionalExtThreeFunctor Q hAS).IsEquivalence :=
  inferInstanceAs (A.finiteDimensionalExtThreeEquivalence Q hAS).functor.IsEquivalence

instance rightFiniteDimensionalVectorDualFunctorIsEquivalence :
    A.rightFiniteDimensionalVectorDualFunctor.IsEquivalence :=
  inferInstanceAs A.finiteDimensionalVectorDualEquivalence.functor.IsEquivalence

instance leftFiniteDimensionalVectorDualFunctorIsEquivalence :
    A.leftFiniteDimensionalVectorDualFunctor.IsEquivalence :=
  inferInstanceAs A.leftFiniteDimensionalVectorDualEquivalence.functor.IsEquivalence

instance rightFiniteDimensionalNakayamaFunctorAdditive (hAS : A.ASRegular Q) :
    (A.rightFiniteDimensionalNakayamaEquivalence Q hAS).functor.Additive := by
  change ( (A.rightFiniteDimensionalExtThreeFunctor Q hAS).rightOp ⋙
    A.leftFiniteDimensionalVectorDualFunctor).Additive
  infer_instance

instance rightFiniteDimensionalNakayamaFunctorLinear (hAS : A.ASRegular Q) :
    (A.rightFiniteDimensionalNakayamaEquivalence Q hAS).functor.Linear k where
  map_smul := by
    intro M N f r
    change A.leftFiniteDimensionalVectorDualFunctor.map
        ((A.rightFiniteDimensionalExtThreeFunctor Q hAS).map (r • f).op).op =
      r • A.leftFiniteDimensionalVectorDualFunctor.map
        ((A.rightFiniteDimensionalExtThreeFunctor Q hAS).map f.op).op
    rw [show (r • f).op = r • f.op from rfl,Functor.map_smul]
    change A.leftFiniteDimensionalVectorDualFunctor.map
        (r • ((A.rightFiniteDimensionalExtThreeFunctor Q hAS).map f.op).op) = _
    exact A.leftFiniteDimensionalVectorDualFunctor.map_smul r _

noncomputable instance rightFiniteDimensionalNakayamaPreservesFiniteLimits (hAS : A.ASRegular Q) :
    PreservesFiniteLimits (A.rightFiniteDimensionalNakayamaEquivalence Q hAS).functor := inferInstance
noncomputable instance rightFiniteDimensionalNakayamaPreservesFiniteColimits (hAS : A.ASRegular Q) :
    PreservesFiniteColimits (A.rightFiniteDimensionalNakayamaEquivalence Q hAS).functor := inferInstance

theorem rightFiniteDimensionalNakayama_shortExact (hAS : A.ASRegular Q)
    {S : ShortComplex A.RightFiniteDimensional} (hS : S.ShortExact) :
    (S.map (A.rightFiniteDimensionalNakayamaEquivalence Q hAS).functor).ShortExact := by
  letI := hS.mono_f
  letI := hS.epi_g
  exact hS.map _
end ASGinzburg.ZAlgebra
